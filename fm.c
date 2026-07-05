#define _XOPEN_SOURCE_EXTENDED
#define _GNU_SOURCE
#include <ctype.h>
#include <dirent.h>
#include <fcntl.h>
#include <libtsm.h>
#include <locale.h>
#include <ncursesw/ncurses.h>
#include <pthread.h>
#include <pty.h>
#include <pwd.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
#include <wchar.h>

#define MAX_TABS 9
#define MAX_ENTRIES 8192
#define MAX_PROCS 4096

typedef struct {
  char name[256];
  off_t size;
  int is_dir;
} Entry;

typedef enum { OP_NONE, OP_COPY, OP_MOVE } YankOp;

typedef struct {
  char cwd[4096];
  Entry *entries;
  int count;
  int cursor;
  int offset;
  int poff;
  int in_use;
} Tab;

typedef struct {
  pid_t pid;
  pid_t ppid;
  unsigned long long starttime;
  char comm[256];
  char cmdline[512];
  char user[64];
} ProcItem;

static int focus = 0;

static int proc_mode = 0;
static int proc_scroll = 0;
static int proc_cursor = 0;
static int proc_count = 0;
static ProcItem proc_items[MAX_PROCS];
static WINDOW *proc_win = NULL;

/* ─── сигнал nvim ────────────────────────────────────────── */
static volatile int nvim_signal = 0;
static char nvim_tmpfile[64] = "";

static void sigusr1_handler(int sig) {
  (void)sig;
  nvim_signal = 1;
}

static volatile int resize_pending = 0;

static void sigwinch_handler(int sig) {
  (void)sig;
  resize_pending = 1;
}

/* ─── PTY / TSM ──────────────────────────────────────────── */

static struct tsm_screen *tsm_scr = NULL;
static struct tsm_vte *tsm_vte = NULL;
static int pty_fd = -1;
static pid_t shell_pid = 0;
static WINDOW *term_win = NULL;
static pthread_mutex_t tsm_lock = PTHREAD_MUTEX_INITIALIZER;
static volatile int pty_dirty = 0;
static volatile int pty_running = 1;

static int draw_cell_cb(struct tsm_screen *scr, unsigned long id,
                        const uint32_t *ch, size_t len, unsigned int width,
                        unsigned int posx, unsigned int posy,
                        const struct tsm_screen_attr *attr, tsm_age_t age,
                        void *data) {
  (void)scr;
  (void)id;
  (void)width;
  (void)age;
  (void)data;
  if (!term_win)
    return 0;
  char buf[8] = {' ', 0};
  if (len > 0) {
    wchar_t wc = (wchar_t)ch[0];
    if (wc > 0)
      wctomb(buf, wc);
  }
  int at = 0;
  if (attr->bold)
    at |= A_BOLD;
  if (attr->underline)
    at |= A_UNDERLINE;
  if (attr->inverse)
    at |= A_REVERSE;
  wattron(term_win, at);
  mvwaddstr(term_win, (int)posy + 1, (int)posx, buf);
  wattroff(term_win, at);
  return 0;
}

static void vte_write_cb(struct tsm_vte *vte, const char *u8, size_t len,
                         void *data) {
  (void)vte;
  (void)data;
  if (pty_fd >= 0)
    write(pty_fd, u8, len);
}

static void *pty_reader(void *arg) {
  (void)arg;
  char buf[4096];
  ssize_t n;
  while (pty_running && (n = read(pty_fd, buf, sizeof(buf))) > 0) {
    pthread_mutex_lock(&tsm_lock);
    tsm_vte_input(tsm_vte, buf, n);
    pty_dirty = 1;
    pthread_mutex_unlock(&tsm_lock);
  }
  return NULL;
}

static void term_init(int rows, int cols, const char *home, pid_t fm_pid) {
  if (rows < 2)
    rows = 2;
  if (cols < 8)
    cols = 8;
  tsm_screen_new(&tsm_scr, NULL, NULL);
  tsm_screen_resize(tsm_scr, cols, rows);
  tsm_vte_new(&tsm_vte, tsm_scr, vte_write_cb, NULL, NULL, NULL);
  struct winsize ws;
  memset(&ws, 0, sizeof(ws));
  ws.ws_row = (unsigned short)rows;
  ws.ws_col = (unsigned short)cols;
  shell_pid = forkpty(&pty_fd, NULL, NULL, &ws);
  if (shell_pid == 0) {
    char bin[4096];
    snprintf(bin, sizeof(bin), "%s/bin", home);
    const char *oldpath = getenv("PATH");
    char newpath[8192];
    snprintf(newpath, sizeof(newpath), "%s:%s", bin,
             oldpath ? oldpath : "/usr/bin:/bin");
    setenv("PATH", newpath, 1);
    char pidstr[32];
    snprintf(pidstr, sizeof(pidstr), "%d", (int)fm_pid);
    setenv("FM_PID", pidstr, 1);
    char *sh = getenv("SHELL");
    if (!sh)
      sh = "/bin/bash";
    execl(sh, sh, NULL);
    exit(1);
  }
  pthread_t tid;
  pthread_create(&tid, NULL, pty_reader, NULL);
  pthread_detach(tid);
}

static void pty_resize(int rows, int cols) {
  struct winsize ws;
  memset(&ws, 0, sizeof(ws));
  ws.ws_row = (unsigned short)rows;
  ws.ws_col = (unsigned short)cols;
  ioctl(pty_fd, TIOCSWINSZ, &ws);
  pthread_mutex_lock(&tsm_lock);
  tsm_screen_resize(tsm_scr, cols, rows);
  pthread_mutex_unlock(&tsm_lock);
}

static void term_draw(void) {
  if (!term_win || !tsm_scr)
    return;
  pthread_mutex_lock(&tsm_lock);
  werase(term_win);
  if (focus == 2)
    wattron(term_win, A_BOLD);
  box(term_win, 0, 0);
  if (focus == 2)
    wattroff(term_win, A_BOLD);
  mvwprintw(term_win, 0, 2, " terminal ");
  tsm_screen_draw(tsm_scr, draw_cell_cb, NULL);
  int cx = (int)tsm_screen_get_cursor_x(tsm_scr);
  int cy = (int)tsm_screen_get_cursor_y(tsm_scr);
  mvwchgat(term_win, cy + 1, cx, 1, A_REVERSE, 0, NULL);
  pty_dirty = 0;
  pthread_mutex_unlock(&tsm_lock);
  wrefresh(term_win);
}

static void term_send_key(int ch) {
  if (pty_fd < 0)
    return;
  pthread_mutex_lock(&tsm_lock);
  switch (ch) {
  case KEY_UP:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF52, 0xFF52, 0, 0);
    break;
  case KEY_DOWN:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF54, 0xFF54, 0, 0);
    break;
  case KEY_LEFT:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF51, 0xFF51, 0, 0);
    break;
  case KEY_RIGHT:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF53, 0xFF53, 0, 0);
    break;
  case KEY_BACKSPACE:
  case 127:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF08, 0xFF08, 0, 0);
    break;
  case '\n':
  case KEY_ENTER:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF0D, 0xFF0D, 0, 0);
    break;
  case 27:
    tsm_vte_handle_keyboard(tsm_vte, 0xFF1B, 0xFF1B, 0, 0);
    break;
  default:
    if (ch >= 1 && ch <= 26) {
      tsm_vte_handle_keyboard(tsm_vte, (uint32_t)('a' + ch - 1),
                              (uint32_t)('a' + ch - 1), 4, ch);
    } else if (ch >= 32 && ch < 127) {
      char c = (char)ch;
      write(pty_fd, &c, 1);
    }
    break;
  }
  pthread_mutex_unlock(&tsm_lock);
}

/* ─── враппер nvim ───────────────────────────────────────── */

static void install_nvim_wrapper(const char *home, pid_t fm_pid) {
  char bin[4096];
  snprintf(bin, sizeof(bin), "%s/bin", home);
  mkdir(bin, 0755);

  char wpath[4096];
  snprintf(wpath, sizeof(wpath), "%s/bin/nvim", home);
  FILE *f = fopen(wpath, "w");
  if (!f)
    return;
  fprintf(f, "#!/bin/sh\n");
  fprintf(f, "printf '%%s' \"$*\" > /tmp/fm_nvim_%d\n", (int)fm_pid);
  fprintf(f, "kill -USR1 %d\n", (int)fm_pid);
  fprintf(f, "while [ -f /tmp/fm_nvim_%d ]; do sleep 0.1; done\n", (int)fm_pid);
  fclose(f);
  chmod(wpath, 0755);

  snprintf(nvim_tmpfile, sizeof(nvim_tmpfile), "/tmp/fm_nvim_%d", (int)fm_pid);
}

static void remove_nvim_wrapper(const char *home) {
  char wpath[4096];
  snprintf(wpath, sizeof(wpath), "%s/bin/nvim", home);
  remove(wpath);
}

/* ─── открытие nvim ──────────────────────────────────────── */

static void open_nvim_path(const char *path) {
  char cmd[4096];
  char real_nvim[256] = "/usr/bin/nvim";
  FILE *w =
      popen("which -a nvim 2>/dev/null | grep -v \"$HOME/bin\" | head -1", "r");
  if (w) {
    fgets(real_nvim, sizeof(real_nvim), w);
    pclose(w);
    real_nvim[strcspn(real_nvim, "\n")] = '\0';
  }
  if (!real_nvim[0])
    strcpy(real_nvim, "nvim");
  snprintf(cmd, sizeof(cmd), "%s \"%s\"", real_nvim, path);
  def_prog_mode();
  endwin();
  system(cmd);
  reset_prog_mode();
  touchwin(stdscr);
  refresh();
}

static void open_nvim(const char *cwd, const char *name) {
  char path[4096];
  snprintf(path, sizeof(path), "%s/%s", cwd, name);
  open_nvim_path(path);
}

/* ─── сортировка ─────────────────────────────────────────── */

static int name_priority(const char *n) {
  if (!strcmp(n, ".."))
    return 0;
  if (n[0] == '.')
    return 3;
  unsigned char c = (unsigned char)n[0];
  return ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) ? 1 : 2;
}
static int cmp_entries(const void *a, const void *b) {
  const Entry *ea = a, *eb = b;
  if (ea->is_dir && !eb->is_dir)
    return -1;
  if (!ea->is_dir && eb->is_dir)
    return 1;
  int pa = name_priority(ea->name), pb = name_priority(eb->name);
  if (pa != pb)
    return pa - pb;
  return strcasecmp(ea->name, eb->name);
}

/* ─── загрузка директории ────────────────────────────────── */

static int load_dir(const char *path, Entry *entries, int max) {
  DIR *dir = opendir(path);
  if (!dir)
    return 0;
  strcpy(entries[0].name, "..");
  entries[0].is_dir = 1;
  entries[0].size = 0;
  int count = 1;
  struct dirent *de;
  while ((de = readdir(dir)) && count < max) {
    if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, ".."))
      continue;
    struct stat st;
    char fp[4096];
    snprintf(fp, sizeof(fp), "%s/%s", path, de->d_name);
    stat(fp, &st);
    strncpy(entries[count].name, de->d_name, 255);
    entries[count].name[255] = '\0';
    entries[count].size = st.st_size;
    entries[count].is_dir = S_ISDIR(st.st_mode);
    count++;
  }
  closedir(dir);
  qsort(entries + 1, count - 1, sizeof(Entry), cmp_entries);
  return count;
}

/* ─── процессы (/proc) ──────────────────────────────────── */

static unsigned long long read_starttime(pid_t pid) {
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d/stat", pid);
  FILE *f = fopen(path, "r");
  if (!f)
    return 0;
  char buf[4096];
  if (!fgets(buf, sizeof(buf), f)) {
    fclose(f);
    return 0;
  }
  fclose(f);
  char *rp = strrchr(buf, ')');
  if (!rp)
    return 0;
  char *p = rp + 2;
  int field = 3;
  char *save = NULL;
  char *tok = strtok_r(p, " ", &save);
  while (tok) {
    if (field == 22)
      return strtoull(tok, NULL, 10);
    tok = strtok_r(NULL, " ", &save);
    field++;
  }
  return 0;
}

static void read_proc_cmdline(pid_t pid, char *out, size_t outsz) {
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d/cmdline", pid);
  FILE *f = fopen(path, "r");
  if (!f) {
    out[0] = '\0';
    return;
  }
  size_t n = fread(out, 1, outsz - 1, f);
  fclose(f);
  if (n == 0) {
    out[0] = '\0';
    return;
  }
  out[n] = '\0';
  for (size_t i = 0; i < n; i++)
    if (out[i] == '\0')
      out[i] = ' ';
}

static void read_proc_comm(pid_t pid, char *out, size_t outsz) {
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d/comm", pid);
  FILE *f = fopen(path, "r");
  if (!f) {
    out[0] = '\0';
    return;
  }
  if (!fgets(out, (int)outsz, f))
    out[0] = '\0';
  fclose(f);
  out[strcspn(out, "\n")] = '\0';
}

static void read_proc_user(pid_t pid, char *out, size_t outsz) {
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d", pid);
  struct stat st;
  if (stat(path, &st) != 0) {
    out[0] = '\0';
    return;
  }
  struct passwd *pwd = getpwuid(st.st_uid);
  if (pwd)
    snprintf(out, outsz, "%s", pwd->pw_name);
  else
    snprintf(out, outsz, "%u", (unsigned)st.st_uid);
}

static int cmp_proc_newest(const void *a, const void *b) {
  const ProcItem *pa = a, *pb = b;
  if (pa->starttime < pb->starttime)
    return 1;
  if (pa->starttime > pb->starttime)
    return -1;
  if (pa->pid < pb->pid)
    return -1;
  if (pa->pid > pb->pid)
    return 1;
  return 0;
}

static void load_processes(void) {
  proc_count = 0;
  DIR *d = opendir("/proc");
  if (!d)
    return;
  struct dirent *de;
  while ((de = readdir(d)) != NULL && proc_count < MAX_PROCS) {
    if (!isdigit((unsigned char)de->d_name[0]))
      continue;
    pid_t pid = (pid_t)atoi(de->d_name);
    ProcItem *p = &proc_items[proc_count];
    memset(p, 0, sizeof(*p));
    p->pid = pid;
    p->starttime = read_starttime(pid);
    if (!p->starttime)
      continue;
    read_proc_comm(pid, p->comm, sizeof(p->comm));
    read_proc_cmdline(pid, p->cmdline, sizeof(p->cmdline));
    if (!p->cmdline[0])
      snprintf(p->cmdline, sizeof(p->cmdline), "%s", p->comm);
    read_proc_user(pid, p->user, sizeof(p->user));
    proc_count++;
  }
  closedir(d);
  qsort(proc_items, proc_count, sizeof(ProcItem), cmp_proc_newest);
}

static void render_process_window(WINDOW *win) {
  int h = getmaxy(win), w = getmaxx(win);
  werase(win);
  box(win, 0, 0);
  mvwprintw(win, 0, 2, " processes (newest first) ");
  mvwprintw(win, 0, w - 24, " P:back  j/k:move ");
  int visible = h - 2;
  for (int i = 0; i < visible; i++) {
    int idx = proc_scroll + i;
    if (idx >= proc_count)
      break;
    if (idx == proc_cursor)
      wattron(win, A_REVERSE);
    ProcItem *p = &proc_items[idx];
    mvwhline(win, i + 1, 1, ' ', w - 2);

    int col = 1;
    mvwprintw(win, i + 1, col, "%7d", p->pid);
    col += 8;

    mvwprintw(win, i + 1, col, "%-10.10s", p->user);
    col += 11;

    mvwprintw(win, i + 1, col, "%-16.16s", p->comm);
    col += 17;

    char cmd[256];
    snprintf(cmd, sizeof(cmd), "%s", p->cmdline);
    if ((int)strlen(cmd) > w - col - 1 && w - col - 1 > 0)
      cmd[w - col - 1] = '\0';
    mvwprintw(win, i + 1, col, "%s", cmd);
    if (idx == proc_cursor)
      wattroff(win, A_REVERSE);
  }
  wrefresh(win);
}

/* ─── вкладки ────────────────────────────────────────────── */

static void tab_init(Tab *t, const char *path) {
  memset(t, 0, sizeof(Tab));
  t->entries = calloc(MAX_ENTRIES, sizeof(Entry));
  if (!t->entries) {
    fprintf(stderr, "oom\n");
    exit(1);
  }
  strncpy(t->cwd, path, 4095);
  t->count = load_dir(path, t->entries, MAX_ENTRIES);
  t->cursor = (t->count > 1) ? 1 : 0;
  t->in_use = 1;
}
static void tab_free(Tab *t) {
  free(t->entries);
  t->entries = NULL;
  t->in_use = 0;
}
static void switch_tab(Tab **T, Tab *tabs, int *prev, int *cur, int nxt,
                       char *search, int *slen, int *srch) {
  *prev = *cur;
  *cur = nxt;
  *T = &tabs[*cur];
  search[0] = '\0';
  *slen = 0;
  *srch = 0;
}

/* ─── навигация ──────────────────────────────────────────── */

static void jump_to_name(Entry *entries, int count, const char *name,
                         int *cursor, int *offset, int wh) {
  for (int i = 0; i < count; i++)
    if (!strcmp(entries[i].name, name)) {
      *cursor = i;
      *offset = (i > wh / 2) ? i - wh / 2 : 0;
      return;
    }
}
static void go_up(Tab *t) {
  char prev[256] = "", np[4096];
  strncpy(np, t->cwd, 4096);
  char *sl = strrchr(np, '/');
  if (sl)
    strncpy(prev, sl + 1, 255);
  if (sl && sl != np)
    *sl = '\0';
  else
    strcpy(np, "/");
  int nc = load_dir(np, t->entries, MAX_ENTRIES);
  if (nc > 0) {
    strcpy(t->cwd, np);
    t->count = nc;
    t->offset = 0;
    t->cursor = 1;
    for (int i = 0; i < nc; i++)
      if (!strcmp(t->entries[i].name, prev)) {
        t->cursor = i;
        break;
      }
  }
}
static void go_into(Tab *t) {
  if (!t->entries[t->cursor].is_dir)
    return;
  if (!strcmp(t->entries[t->cursor].name, "..")) {
    go_up(t);
    return;
  }
  char np[4096];
  snprintf(np, sizeof(np), "%s/%s", t->cwd, t->entries[t->cursor].name);
  int nc = load_dir(np, t->entries, MAX_ENTRIES);
  if (nc > 0) {
    strcpy(t->cwd, np);
    t->count = nc;
    t->cursor = (nc > 1) ? 1 : 0;
    t->offset = 0;
  }
}

/* ─── поиск ──────────────────────────────────────────────── */

static int is_text(const char *name) {
  const char *e = strrchr(name, '.');
  if (!e)
    return 1;
  const char *ok[] = {".c",    ".h",    ".cpp",  ".py",  ".go",   ".js",
                      ".ts",   ".rs",   ".md",   ".txt", ".json", ".yaml",
                      ".toml", ".sh",   ".html", ".css", ".sql",  ".xml",
                      ".ini",  ".conf", ".lua",  NULL};
  for (int i = 0; ok[i]; i++)
    if (!strcmp(e, ok[i]))
      return 1;
  return 0;
}

static int matches(const char *name, const char *q) {
  if (!q[0])
    return 1;
  char nl[256], ql[256];
  strncpy(nl, name, 255);
  nl[255] = '\0';
  strncpy(ql, q, 255);
  ql[255] = '\0';
  for (int i = 0; nl[i]; i++)
    nl[i] = tolower(nl[i]);
  for (int i = 0; ql[i]; i++)
    ql[i] = tolower(ql[i]);
  return strstr(nl, ql) != NULL;
}

/* ─── диалоги ────────────────────────────────────────────── */

static int input_dialog(WINDOW *parent, const char *title, char *result,
                        int max, const char *init) {
  int rows = getmaxy(parent), cols = getmaxx(parent);
  int w = 52, h = 3;
  WINDOW *d = newwin(h, w, rows / 2 - h / 2, cols / 2 - w / 2);
  keypad(d, TRUE);
  box(d, 0, 0);
  mvwprintw(d, 0, 2, " %s ", title);
  char buf[256] = "";
  int len = 0;
  if (init && init[0]) {
    strncpy(buf, init, 255);
    len = strlen(buf);
  }
  mvwprintw(d, 1, 1, "%s_", buf);
  wrefresh(d);
  int ch;
  while ((ch = wgetch(d)) != '\n' && ch != KEY_ENTER) {
    if (ch == 27) {
      delwin(d);
      touchwin(parent);
      return 0;
    }
    if ((ch == KEY_BACKSPACE || ch == 127) && len > 0)
      buf[--len] = '\0';
    else if (ch >= 32 && ch < 127 && len < max - 1) {
      buf[len++] = ch;
      buf[len] = '\0';
    }
    mvwhline(d, 1, 1, ' ', w - 2);
    mvwprintw(d, 1, 1, "%s_", buf);
    wrefresh(d);
  }
  delwin(d);
  touchwin(parent);
  strncpy(result, buf, max);
  return len > 0;
}
static int confirm_dialog(WINDOW *parent, const char *msg) {
  int rows = getmaxy(parent), cols = getmaxx(parent);
  int w = 56, h = 3;
  WINDOW *d = newwin(h, w, rows / 2 - h / 2, cols / 2 - w / 2);
  keypad(d, TRUE);
  box(d, 0, 0);
  mvwprintw(d, 0, 2, " Confirm ");
  mvwaddnstr(d, 1, 1, msg, w - 2);
  wrefresh(d);
  int ch = wgetch(d);
  delwin(d);
  touchwin(parent);
  return (ch == 'y' || ch == 'Y');
}

/* ─── файловые операции ──────────────────────────────────── */

static void create_file(const char *cwd, const char *name) {
  char p[4096];
  snprintf(p, sizeof(p), "%s/%s", cwd, name);
  FILE *f = fopen(p, "w");
  if (f)
    fclose(f);
}
static void create_dir(const char *cwd, const char *name) {
  char p[4096];
  snprintf(p, sizeof(p), "%s/%s", cwd, name);
  mkdir(p, 0755);
}
static void delete_recursive(const char *path) {
  struct stat st;
  if (lstat(path, &st) != 0)
    return;
  if (!S_ISDIR(st.st_mode)) {
    remove(path);
    return;
  }
  DIR *dir = opendir(path);
  if (!dir) {
    rmdir(path);
    return;
  }
  struct dirent *de;
  while ((de = readdir(dir)) != NULL) {
    if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, ".."))
      continue;
    char child[4096];
    snprintf(child, sizeof(child), "%s/%s", path, de->d_name);
    delete_recursive(child);
  }
  closedir(dir);
  rmdir(path);
}
static void rename_entry(const char *cwd, const char *old, const char *nw) {
  char op[4096], np[4096];
  snprintf(op, sizeof(op), "%s/%s", cwd, old);
  snprintf(np, sizeof(np), "%s/%s", cwd, nw);
  rename(op, np);
}
static int copy_file(const char *src, const char *dst) {
  int in = open(src, O_RDONLY);
  if (in < 0)
    return -1;
  struct stat st;
  fstat(in, &st);
  int out = open(dst, O_WRONLY | O_CREAT | O_TRUNC, st.st_mode);
  if (out < 0) {
    close(in);
    return -1;
  }
  char buf[65536];
  ssize_t n, wr;
  int ok = 1;
  while ((n = read(in, buf, sizeof(buf))) > 0) {
    wr = write(out, buf, n);
    if (wr != n) {
      ok = 0;
      break;
    }
  }
  close(in);
  close(out);
  if (!ok)
    remove(dst);
  return ok ? 0 : -1;
}
static int copy_dir_r(const char *src, const char *dst) {
  mkdir(dst, 0755);
  DIR *dir = opendir(src);
  if (!dir)
    return -1;
  struct dirent *de;
  while ((de = readdir(dir)) != NULL) {
    if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, ".."))
      continue;
    char sp[4096], dp[4096];
    snprintf(sp, sizeof(sp), "%s/%s", src, de->d_name);
    snprintf(dp, sizeof(dp), "%s/%s", dst, de->d_name);
    struct stat st;
    stat(sp, &st);
    if (S_ISDIR(st.st_mode))
      copy_dir_r(sp, dp);
    else
      copy_file(sp, dp);
  }
  closedir(dir);
  return 0;
}
static void do_copy(const char *sd, const char *name, const char *dd,
                    const char *dn) {
  char src[4096], dst[4096];
  snprintf(src, sizeof(src), "%s/%s", sd, name);
  snprintf(dst, sizeof(dst), "%s/%s", dd, dn);
  struct stat st;
  stat(src, &st);
  if (S_ISDIR(st.st_mode))
    copy_dir_r(src, dst);
  else
    copy_file(src, dst);
}
static void do_move(const char *sd, const char *name, const char *dd,
                    const char *dn) {
  char src[4096], dst[4096];
  snprintf(src, sizeof(src), "%s/%s", sd, name);
  snprintf(dst, sizeof(dst), "%s/%s", dd, dn);
  if (rename(src, dst) == 0)
    return;
  do_copy(sd, name, dd, dn);
  delete_recursive(src);
}

/* ─── отрисовка ──────────────────────────────────────────── */

static void render_tabbar(WINDOW *win, Tab *tabs, int ntabs, int cur,
                          int prev_t) {
  werase(win);
  int x = 0;
  for (int i = 0; i < ntabs; i++) {
    const char *sl = strrchr(tabs[i].cwd, '/');
    const char *label = sl ? sl + 1 : tabs[i].cwd;
    if (!label[0])
      label = "/";
    char buf[36];
    snprintf(buf, sizeof(buf), i == prev_t && i != cur ? " %d·%s " : " %d:%s ",
             i + 1, label);
    if (i == cur)
      wattron(win, A_REVERSE | A_BOLD);
    mvwaddnstr(win, 0, x, buf, getmaxx(win) - x - 1);
    if (i == cur)
      wattroff(win, A_REVERSE | A_BOLD);
    x += (int)strlen(buf) + 1;
    if (x >= getmaxx(win) - 16)
      break;
  }
  const char *hint = " t:new x:close";
  mvwaddstr(win, 0, getmaxx(win) - (int)strlen(hint), hint);
  wrefresh(win);
}

static void render_panel(WINDOW *win, Tab *t, const char *filter,
                         const char *yank_name, YankOp yop) {
  int wh = getmaxy(win) - 2, nw = getmaxx(win) - 11;
  werase(win);
  if (focus == 0)
    wattron(win, A_BOLD);
  box(win, 0, 0);
  if (focus == 0)
    wattroff(win, A_BOLD);
  mvwprintw(win, 0, 2, " %s ", t->cwd);
  int row = 1;
  for (int i = t->offset; i < t->count && row <= wh; i++) {
    if (!matches(t->entries[i].name, filter))
      continue;
    int is_cur = (i == t->cursor);
    if (is_cur)
      wattron(win, A_REVERSE);
    wchar_t wn[256];
    mbstowcs(wn, t->entries[i].name, 256);
    mvwhline(win, row, 1, ' ', getmaxx(win) - 2);
    mvwaddnwstr(win, row, 1, wn, nw);
    char sz[16];
    if (t->entries[i].is_dir)
      snprintf(sz, sizeof(sz), "<DIR>");
    else
      snprintf(sz, sizeof(sz), "%d", (int)t->entries[i].size);
    mvwprintw(win, row, getmaxx(win) - 9, "%8s", sz);
    if (is_cur)
      wattroff(win, A_REVERSE);
    row++;
  }
  wrefresh(win);
}

static void render_preview(WINDOW *win, Tab *t) {
  int wh = getmaxy(win) - 2, ww = getmaxx(win) - 2;
  Entry *entry = &t->entries[t->cursor];
  int poff = t->poff;
  werase(win);
  if (focus == 1)
    wattron(win, A_BOLD);
  box(win, 0, 0);
  if (focus == 1)
    wattroff(win, A_BOLD);
  if (entry->is_dir) {
    char path[4096];
    if (!strcmp(entry->name, ".."))
      strncpy(path, t->cwd, 4096);
    else
      snprintf(path, sizeof(path), "%s/%s", t->cwd, entry->name);
    mvwprintw(win, 0, 2, " %s/ ", entry->name);
    Entry *pv = calloc(512, sizeof(Entry));
    if (pv) {
      int cnt = load_dir(path, pv, 512);
      for (int i = poff; i < cnt && (i - poff) < wh; i++) {
        wchar_t wn[256];
        mbstowcs(wn, pv[i].name, 256);
        mvwaddnwstr(win, i - poff + 1, 1, wn, ww);
      }
      free(pv);
    }
  } else {
    mvwprintw(win, 0, 2, " %s ", entry->name);
    if (!is_text(entry->name)) {
      mvwprintw(win, 1, 1, "[binary]");
      mvwprintw(win, 2, 1, "size: %lld bytes", (long long)entry->size);
    } else {
      char p[4096];
      snprintf(p, sizeof(p), "%s/%s", t->cwd, entry->name);
      FILE *f = fopen(p, "r");
      if (f) {
        char line[512];
        int row = 1, ln = 0;
        while (fgets(line, sizeof(line), f) && row <= wh) {
          ln++;
          if (ln <= poff)
            continue;
          line[strcspn(line, "\n")] = '\0';
          mvwaddnstr(win, row, 1, line, ww);
          row++;
        }
        fclose(f);
      } else
        mvwprintw(win, 1, 1, "[no permission]");
    }
  }
  if (poff > 0)
    mvwprintw(win, 0, getmaxx(win) - 8, " L%-4d ", poff + 1);
  wrefresh(win);
}

static void render_status(WINDOW *win, Tab *t, int searching,
                          const char *search, const char *yank_name,
                          YankOp yop) {
  werase(win);
  wattron(win, A_REVERSE);
  int width = getmaxx(win);
  Entry *e = &t->entries[t->cursor];
  if (searching) {
    mvwprintw(win, 0, 0, " /%s_", search);
  } else if (focus == 2) {
    mvwaddnstr(win, 0, 0, " TERMINAL  S-Tab: back to panel", width - 66);
  } else if (focus == 0) {
    char info[512];
    if (e->is_dir)
      snprintf(info, sizeof(info), " [DIR] %s/%s", t->cwd, e->name);
    else
      snprintf(info, sizeof(info), " %s/%s  (%lld bytes)", t->cwd, e->name,
               (long long)e->size);
    mvwaddnstr(win, 0, 0, info, width - 66);
  } else {
    mvwaddnstr(win, 0, 0, " PREVIEW  j/k scroll  Enter nvim  h back",
               width - 66);
  }
  if (yank_name[0] && focus != 2) {
    char yi[300];
    snprintf(yi, sizeof(yi), " [%s: %s] ", yop == OP_MOVE ? "mv" : "cp",
             yank_name);
    mvwaddnstr(win, 0, width - 66 + 2, yi, 34);
  }
  if (!searching && focus != 2) {
    const char *hint = " a|A new  y|m yank  p paste  r rename  d del  / search "
                       " P proc  S-Tab term  q quit ";
    int hl = (int)strlen(hint);
    if (hl < width)
      mvwaddstr(win, 0, width - hl, hint);
  }
  wattroff(win, A_REVERSE);
  wrefresh(win);
}

static void relayout(WINDOW **tabbar, WINDOW **panel, WINDOW **prev_w,
                     WINDOW *term_win_ptr, WINDOW **status, WINDOW **proc_win,
                     int *rows, int *cols) {
  endwin();
  refresh();
  clear();
  getmaxyx(stdscr, *rows, *cols);

  int half = *cols / 2;
  int content = *rows - 2;
  int panel_h = content / 2;
  int term_h = content - panel_h;

  wresize(*tabbar, 1, *cols);
  mvwin(*tabbar, 0, 0);

  wresize(*panel, panel_h, half);
  mvwin(*panel, 1, 0);

  wresize(*prev_w, content, *cols - half);
  mvwin(*prev_w, 1, half);

  wresize(term_win_ptr, term_h, half);
  mvwin(term_win_ptr, 1 + panel_h, 0);

  wresize(*status, 1, *cols);
  mvwin(*status, *rows - 1, 0);

  if (*proc_win) {
    wresize(*proc_win, *rows - 2, *cols);
    mvwin(*proc_win, 1, 0);
  }

  pty_resize(term_h - 2, half - 2);

  touchwin(*tabbar);
  touchwin(*panel);
  touchwin(*prev_w);
  touchwin(term_win_ptr);
  touchwin(*status);
  if (*proc_win)
    touchwin(*proc_win);
}

/* ─── main ───────────────────────────────────────────────── */

int main(void) {
  setlocale(LC_ALL, "");

  char home[4096];
  struct passwd *pw = getpwuid(getuid());
  strncpy(home, pw ? pw->pw_dir : "/", 4096);

  pid_t fm_pid = getpid();

  signal(SIGUSR1, sigusr1_handler);
  signal(SIGWINCH, sigwinch_handler);

  install_nvim_wrapper(home, fm_pid);

  Tab tabs[MAX_TABS];
  memset(tabs, 0, sizeof(tabs));
  int ntabs = 1, cur_tab = 0, prev_tab = 0;
  tab_init(&tabs[0], home);

  char yank_src[4096] = "", yank_name[256] = "";
  YankOp yank_op = OP_NONE;
  int searching = 0;
  char search[256] = "";
  int search_len = 0;

  initscr();
  cbreak();
  noecho();
  int rows, cols;
  getmaxyx(stdscr, rows, cols);
  refresh();

  int half = cols / 2;
  int content = rows - 2;
  int panel_h = content / 2;
  int term_h = content - panel_h;

  WINDOW *tabbar = newwin(1, cols, 0, 0);
  WINDOW *panel = newwin(panel_h, half, 1, 0);
  WINDOW *prev_w = newwin(content, cols - half, 1, half);
  term_win = newwin(term_h, half, 1 + panel_h, 0);
  WINDOW *status = newwin(1, cols, rows - 1, 0);

  keypad(panel, TRUE);
  keypad(prev_w, TRUE);
  keypad(term_win, TRUE);

  term_init(term_h - 2, half - 2, home, fm_pid);

  Tab *T = &tabs[cur_tab];

#define REDRAW()                                                               \
  do {                                                                         \
    if (proc_mode) {                                                           \
      render_process_window(proc_win);                                         \
      werase(status);                                                          \
      wattron(status, A_REVERSE);                                              \
      mvwprintw(                                                               \
          status, 0, 0,                                                        \
          " processes: j/k move  Enter kill -9  s signal  P back  q quit ");   \
      wattroff(status, A_REVERSE);                                             \
      wrefresh(status);                                                        \
    } else {                                                                   \
      render_tabbar(tabbar, tabs, ntabs, cur_tab, prev_tab);                   \
      render_panel(panel, T, search, yank_name, yank_op);                      \
      render_preview(prev_w, T);                                               \
      term_draw();                                                             \
      render_status(status, T, searching, search, yank_name, yank_op);         \
    }                                                                          \
  } while (0)

  wtimeout(panel, 50);
  wtimeout(prev_w, 50);
  wtimeout(term_win, 50);

  REDRAW();

  int ch;
  for (;;) {

    if (nvim_signal) {
      nvim_signal = 0;
      char fpath[4096] = "";
      FILE *f = fopen(nvim_tmpfile, "r");
      if (f) {
        fgets(fpath, sizeof(fpath), f);
        fclose(f);
        fpath[strcspn(fpath, "\n")] = '\0';
      }
      if (fpath[0])
        open_nvim_path(fpath);
      else
        open_nvim_path("");
      remove(nvim_tmpfile);
      touchwin(stdscr);
      REDRAW();
      continue;
    }

    if (resize_pending) {
      resize_pending = 0;
      relayout(&tabbar, &panel, &prev_w, term_win, &status, &proc_win, &rows,
               &cols);
      REDRAW();
      continue;
    }

    if (pty_dirty)
      term_draw();

    WINDOW *active_win = proc_mode      ? proc_win
                         : (focus == 0) ? panel
                         : (focus == 1) ? prev_w
                                        : term_win;
    ch = wgetch(active_win);

    if (ch == ERR)
      continue;

    if (proc_mode) {
      int visible = getmaxy(proc_win) - 2;
      if (ch == 'q')
        break;
      if (ch == 'P') {
        proc_mode = 0;
        touchwin(stdscr);
        REDRAW();
        continue;
      } else if (ch == '\n' || ch == KEY_ENTER) {
        if (proc_count > 0) {
          pid_t target = proc_items[proc_cursor].pid;
          char msg[128];
          snprintf(msg, sizeof(msg), "Kill PID %d with SIGKILL? (y/n)",
                   (int)target);
          if (confirm_dialog(proc_win, msg)) {
            kill(target, SIGKILL);
            load_processes();
            if (proc_cursor >= proc_count)
              proc_cursor = proc_count - 1;
            if (proc_cursor < 0)
              proc_cursor = 0;
            if (proc_cursor < proc_scroll)
              proc_scroll = proc_cursor;
          }
        }
      } else if (ch == 's') {
        if (proc_count > 0) {
          pid_t target = proc_items[proc_cursor].pid;
          char sigstr[16] = "15";
          char title[64];
          snprintf(title, sizeof(title), "Signal for PID %d", (int)target);
          if (input_dialog(proc_win, title, sigstr, sizeof(sigstr), "15")) {
            int signum = atoi(sigstr);
            if (signum > 0 && signum < 64) {
              kill(target, signum);
              load_processes();
              if (proc_cursor >= proc_count)
                proc_cursor = proc_count - 1;
              if (proc_cursor < 0)
                proc_cursor = 0;
              if (proc_cursor < proc_scroll)
                proc_scroll = proc_cursor;
            }
          }
        }
      } else if (ch == 'j' || ch == KEY_DOWN) {
        if (proc_cursor < proc_count - 1)
          proc_cursor++;
        if (proc_cursor >= proc_scroll + visible)
          proc_scroll++;
      } else if (ch == 'k' || ch == KEY_UP) {
        if (proc_cursor > 0)
          proc_cursor--;
        if (proc_cursor < proc_scroll)
          proc_scroll--;
        if (proc_scroll < 0)
          proc_scroll = 0;
      } else if (ch == KEY_PPAGE) {
        proc_cursor -= visible;
        if (proc_cursor < 0)
          proc_cursor = 0;
        proc_scroll -= visible;
        if (proc_scroll < 0)
          proc_scroll = 0;
      } else if (ch == 't' && ntabs < MAX_TABS) {
        tab_init(&tabs[ntabs], T->cwd);
        switch_tab(&T, tabs, &prev_tab, &cur_tab, ntabs, search, &search_len,
                   &searching);
        ntabs++;
        proc_mode = 0;
        touchwin(stdscr);
      }
      REDRAW();
      continue;
    }

    if (ch == 'q' && focus != 2)
      break;

    if (ch == 'P') {
      if (!proc_win)
        proc_win = newwin(rows - 2, cols, 1, 0);
      keypad(proc_win, TRUE);
      wtimeout(proc_win, 50);
      load_processes();
      proc_scroll = 0;
      proc_cursor = 0;
      proc_mode = 1;
      REDRAW();
      continue;
    }

    if (ch == KEY_BTAB) {
      focus = (focus == 2) ? 0 : 2;
      REDRAW();
      continue;
    }

    if (focus == 2) {
      term_send_key(ch);
      term_draw();
      continue;
    }

    if (ch == '\t' && !searching) {
      if (prev_tab < ntabs && prev_tab != cur_tab)
        switch_tab(&T, tabs, &prev_tab, &cur_tab, prev_tab, search, &search_len,
                   &searching);
      REDRAW();
      continue;
    }

    if (ch >= '1' && ch <= '9' && !searching) {
      int idx = ch - '1';
      if (idx < ntabs && idx != cur_tab)
        switch_tab(&T, tabs, &prev_tab, &cur_tab, idx, search, &search_len,
                   &searching);
      REDRAW();
      continue;
    }

    if (ch == 't' && !searching && ntabs < MAX_TABS) {
      tab_init(&tabs[ntabs], T->cwd);
      switch_tab(&T, tabs, &prev_tab, &cur_tab, ntabs, search, &search_len,
                 &searching);
      ntabs++;
      REDRAW();
      continue;
    }

    if (ch == 'x' && !searching && ntabs > 1) {
      tab_free(&tabs[cur_tab]);
      for (int i = cur_tab; i < ntabs - 1; i++)
        tabs[i] = tabs[i + 1];
      tabs[ntabs - 1].entries = NULL;
      ntabs--;
      if (prev_tab > cur_tab)
        prev_tab--;
      if (prev_tab >= ntabs)
        prev_tab = ntabs - 1;
      int go = (cur_tab >= ntabs) ? ntabs - 1 : cur_tab;
      if (prev_tab == go && go > 0)
        prev_tab = go - 1;
      cur_tab = go;
      T = &tabs[cur_tab];
      search[0] = '\0';
      search_len = 0;
      searching = 0;
      REDRAW();
      continue;
    }

    if (focus == 1) {
      if (ch == 'j' || ch == KEY_DOWN)
        T->poff++;
      else if ((ch == 'k' || ch == KEY_UP) && T->poff)
        T->poff--;
      else if (ch == 'h' || ch == KEY_LEFT)
        focus = 0;
      else if ((ch == '\n' || ch == KEY_ENTER) &&
               !T->entries[T->cursor].is_dir &&
               is_text(T->entries[T->cursor].name))
        open_nvim(T->cwd, T->entries[T->cursor].name);
      REDRAW();
      continue;
    }

    if (searching) {
      if (ch == 27) {
        searching = 0;
        search[0] = '\0';
        search_len = 0;
        T->cursor = (T->count > 1) ? 1 : 0;
        T->offset = 0;
      } else if (ch == '\n' || ch == KEY_ENTER) {
        searching = 0;
      } else if ((ch == KEY_BACKSPACE || ch == 127) && search_len > 0) {
        search[--search_len] = '\0';
      } else if (ch >= 32 && ch < 127 && search_len < 255) {
        search[search_len++] = ch;
        search[search_len] = '\0';
        for (int i = 0; i < T->count; i++)
          if (matches(T->entries[i].name, search)) {
            T->cursor = i;
            T->offset = (T->cursor > 2) ? T->cursor - 2 : 0;
            break;
          }
      }
      REDRAW();
      continue;
    }

    if (ch == '/') {
      searching = 1;
      search[0] = '\0';
      search_len = 0;
    }

    if (ch == 'a') {
      char name[256] = "";
      if (input_dialog(panel, "New file", name, 256, "")) {
        create_file(T->cwd, name);
        T->count = load_dir(T->cwd, T->entries, MAX_ENTRIES);
        jump_to_name(T->entries, T->count, name, &T->cursor, &T->offset,
                     getmaxy(panel) - 2);
      }
    }
    if (ch == 'A') {
      char name[256] = "";
      if (input_dialog(panel, "New directory", name, 256, "")) {
        create_dir(T->cwd, name);
        T->count = load_dir(T->cwd, T->entries, MAX_ENTRIES);
        jump_to_name(T->entries, T->count, name, &T->cursor, &T->offset,
                     getmaxy(panel) - 2);
      }
    }
    if (ch == 'y' && strcmp(T->entries[T->cursor].name, "..")) {
      strncpy(yank_src, T->cwd, 4095);
      yank_src[4095] = '\0';
      strncpy(yank_name, T->entries[T->cursor].name, 255);
      yank_name[255] = '\0';
      yank_op = OP_COPY;
    }
    if (ch == 'm' && strcmp(T->entries[T->cursor].name, "..")) {
      strncpy(yank_src, T->cwd, 4095);
      yank_src[4095] = '\0';
      strncpy(yank_name, T->entries[T->cursor].name, 255);
      yank_name[255] = '\0';
      yank_op = OP_MOVE;
    }
    if (ch == 'p' && yank_name[0] && yank_op != OP_NONE) {
      char dst_name[256];
      if (yank_op == OP_COPY && !strcmp(yank_src, T->cwd))
        snprintf(dst_name, sizeof(dst_name), "%s_copy", yank_name);
      else {
        strncpy(dst_name, yank_name, 255);
        dst_name[255] = '\0';
      }
      if (yank_op == OP_COPY)
        do_copy(yank_src, yank_name, T->cwd, dst_name);
      else
        do_move(yank_src, yank_name, T->cwd, dst_name);
      yank_name[0] = '\0';
      yank_src[0] = '\0';
      yank_op = OP_NONE;
      T->count = load_dir(T->cwd, T->entries, MAX_ENTRIES);
      jump_to_name(T->entries, T->count, dst_name, &T->cursor, &T->offset,
                   getmaxy(panel) - 2);
    }
    if (ch == 'r' && strcmp(T->entries[T->cursor].name, "..")) {
      char new_name[256];
      strncpy(new_name, T->entries[T->cursor].name, 255);
      new_name[255] = '\0';
      if (input_dialog(panel, "Rename", new_name, 256,
                       T->entries[T->cursor].name)) {
        rename_entry(T->cwd, T->entries[T->cursor].name, new_name);
        T->count = load_dir(T->cwd, T->entries, MAX_ENTRIES);
        jump_to_name(T->entries, T->count, new_name, &T->cursor, &T->offset,
                     getmaxy(panel) - 2);
      }
    }
    if (ch == 'd' && strcmp(T->entries[T->cursor].name, "..")) {
      char msg[512];
      snprintf(msg, sizeof(msg), "Delete \"%s\"? (y/n)",
               T->entries[T->cursor].name);
      if (confirm_dialog(panel, msg)) {
        char fp[4096];
        snprintf(fp, sizeof(fp), "%s/%s", T->cwd, T->entries[T->cursor].name);
        delete_recursive(fp);
        T->count = load_dir(T->cwd, T->entries, MAX_ENTRIES);
        if (T->cursor >= T->count)
          T->cursor = T->count - 1;
        if (T->cursor < 1 && T->count > 1)
          T->cursor = 1;
      }
    }

    if (ch == 'j' || ch == KEY_DOWN) {
      for (int i = T->cursor + 1; i < T->count; i++)
        if (matches(T->entries[i].name, search)) {
          T->cursor = i;
          T->poff = 0;
          break;
        }
    } else if (ch == 'k' || ch == KEY_UP) {
      for (int i = T->cursor - 1; i >= 0; i--)
        if (matches(T->entries[i].name, search)) {
          T->cursor = i;
          T->poff = 0;
          break;
        }
    } else if (ch == 'l' || ch == KEY_RIGHT) {
      if (T->entries[T->cursor].is_dir) {
        go_into(T);
        search[0] = '\0';
        search_len = 0;
      } else {
        focus = 1;
        T->poff = 0;
      }
    } else if (ch == '\n' || ch == KEY_ENTER) {
      if (T->entries[T->cursor].is_dir) {
        go_into(T);
        search[0] = '\0';
        search_len = 0;
      }
    } else if (ch == 'h' || ch == KEY_LEFT || ch == KEY_BACKSPACE ||
               ch == 127) {
      go_up(T);
      search[0] = '\0';
      search_len = 0;
      T->poff = 0;
    }

    int wh = getmaxy(panel) - 2;
    if (T->cursor >= T->offset + wh)
      T->offset = T->cursor - wh + 1;
    if (T->cursor < T->offset)
      T->offset = T->cursor;

    REDRAW();
  }

  remove_nvim_wrapper(home);
  remove(nvim_tmpfile);
  pty_running = 0;
  if (shell_pid > 0)
    kill(shell_pid, SIGTERM);
  if (pty_fd >= 0)
    close(pty_fd);
  if (tsm_vte)
    tsm_vte_unref(tsm_vte);
  if (tsm_scr)
    tsm_screen_unref(tsm_scr);
  for (int i = 0; i < ntabs; i++)
    tab_free(&tabs[i]);
  endwin();
  return 0;
}

#ifndef _TERM_H
#define _TERM_H

#include <stdbool.h>

enum tt {
  TVAR,
  TLAM,
  TAPP,
  TPI,
  TTYPE,
  TEQ,
  TREFL,
  TNAT,
  TZERO,
  TSUCC,
};

struct term {
  enum tt tt;
  union {
    struct {
      char *n;
    } v;
    struct {
      char *x;
      struct term *ty;
      struct term *b;
    } l;
    struct {
      struct term *lam;
      struct term *arg;
    } a;
    struct {
      // (x:A) -> B
      char *x;
      struct term *ta;
      struct term *tb;
    } pi;
    struct {
      // Eq:A l r
      struct term *ty;
      struct term *l, *r;
    } eq;
    struct {
      // Refl a: (Eq:A a a)
      struct term *a;
    } refl;
    struct {
      // Succ (p: Nat): Nat
      struct term *p;
    } succ;
  };
};

struct ctx {
  char *name[128];
  struct term *ty[128];
  int n;
};

struct term *Var(char *n);
struct term *Lam(char *x, struct term *ty, struct term *b);
struct term *App(struct term *lam, struct term *arg);
struct term *Pi(char *x, struct term *ta, struct term *tb);
struct term *Type();
struct term *Eq(struct term *ty, struct term *l, struct term *r);
struct term *Refl(struct term *a);
struct term *Nat ();
struct term *Zero ();
struct term *Succ (struct term *p);
void dump(struct term *t);
struct term *infer(struct ctx *c, struct term *t);
struct ctx *addctx(struct ctx *c, char *name, struct term *ty);
bool equal(struct term *t1, struct term *t2);

#endif

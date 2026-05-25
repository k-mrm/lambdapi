#ifndef _TERM_H
#define _TERM_H

#include <stdbool.h>

enum tt {
  TVAR,
  TLAM,
  TAPP,
  TPI,
  TSIGMA,
  TPAIR,
  TTYPE,
  TEQ,
  TREFL,
  TNAT,
  TZERO,
  TSUCC,
  TNATREC,
  TJ,
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
      struct term *ta, *tb;
    } pi;
    struct {
      // Sigma(x : A). B
      char *x;
      struct term *ta, *tb;
    } s;
    struct {
      // (a, b): Sigma(a: A). B;
      struct term *a, *b;
      struct term *ty;
    } pair;
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
    struct {
      // NatRec: (P: Nat -> Type) -> P Zero -> ((k: Nat) -> P k -> P (Succ k)) -> (m: Nat) -> P m
      struct term *p, *z, *s, *m;
    } natrec;
    struct {
      // J: (A: Type) -> (a: A) -> (P: (b: A) -> Eq A a b -> Type) -> P a (Refl a) -> (b: A) -> (p: Eq A a b) -> P b p
      struct term *ty, *a, *p, *r, *b, *peq;
    } j;
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
struct term *Sigma (char *x, struct term *ta, struct term *tb);
struct term *Pair (struct term *a, struct term *b, struct term *ty);
struct term *Type();
struct term *Eq(struct term *ty, struct term *l, struct term *r);
struct term *Refl(struct term *a);
struct term *Nat ();
struct term *Zero ();
struct term *Succ (struct term *p);
struct term *NatRec (struct term *p, struct term *z, struct term *s, struct term *m);
struct term *J(struct term *ty, struct term *a, struct term *p, struct term *r, struct term *b, struct term *peq);
void dump(struct term *t);
struct term *infer(struct ctx *c, struct term *t);
struct ctx *addctx(struct ctx *c, char *name, struct term *ty);
struct term *norm (struct term *t);
bool equal(struct term *t1, struct term *t2);

#endif

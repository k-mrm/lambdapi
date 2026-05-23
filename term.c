#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include "term.h"

void panic(char *msg) {
  fprintf(stderr, "%s\n", msg);
  exit(1);
}

struct ctx *addctx(struct ctx *c, char *name, struct term *ty) {
  c->name[c->n] = name;
  c->ty[c->n] = ty;
  c->n++;
  return c;
}

struct ctx *ccopy(struct ctx *c) {
  struct ctx *nc;
  nc = malloc(sizeof *nc);
  nc->n = c->n;
  for (int i = 0; i < nc->n; i++) {
    nc->name[i] = c->name[i];
    nc->ty[i] = c->ty[i];
  }
  return nc;
}

struct term *ctx(struct ctx *c, char *name) {
  for (int i = 0; i < c->n; i++) {
    if (strcmp(c->name[i], name) == 0)
      return c->ty[i];
  }
  return NULL;
}

struct term *Var(char *n) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TVAR;
  t->v.n = n;
  return t;
}

struct term *Lam(char *x, struct term *ty, struct term *b) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TLAM;
  t->l.x = x;
  t->l.ty = ty;
  t->l.b = b;
  return t;
}

struct term *App(struct term *lam, struct term *arg) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TAPP;
  t->a.lam = lam;
  t->a.arg = arg;
  return t;
}

struct term *Pi(char *x, struct term *ta, struct term *tb) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TPI;
  t->pi.x = x;
  t->pi.ta = ta;
  t->pi.tb = tb;
  return t;
}

struct term *Type() {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TTYPE;
  return t;
}

struct term *Eq(struct term *ty, struct term *l, struct term *r) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TEQ;
  t->eq.ty = ty;
  t->eq.l = l;
  t->eq.r = r;
  return t;
}

struct term *Refl(struct term *a) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TREFL;
  t->refl.a = a;
  return t;
}

struct term *Nat () {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TNAT;
  return t;
}

struct term *Zero () {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TZERO;
  return t;
}

struct term *Succ (struct term *p) {
  struct term *t;
  t = malloc(sizeof *t);
  if (!t)
    return NULL;
  t->tt = TSUCC;
  t->succ.p = p;
  return t;
}

struct term *betar(struct term *t, char *x, struct term *v) {
  switch (t->tt) {
    case TVAR:
      if (strcmp(t->v.n, x) == 0)
        return v;
      else
        return Var(t->v.n);
    case TLAM:
      if (strcmp(t->l.x, x) != 0)
        return Lam(t->l.x, betar(t->l.ty, x, v), betar(t->l.b, x, v));
      else
        return Lam(t->l.x, betar(t->l.ty, x, v), t->l.b);
    case TAPP:
      return App(betar(t->a.lam, x, v), betar(t->a.arg, x, v));
    case TPI:
      if (strcmp(t->pi.x, x) != 0)
        return Pi(t->pi.x, betar(t->pi.ta, x, v), betar(t->pi.tb, x, v));
      else
        return Pi(t->pi.x, betar(t->pi.ta, x, v), t->pi.tb);
    case TTYPE:
      return Type();
    case TEQ:
      return Eq(betar(t->eq.ty, x, v), betar(t->eq.l, x, v), betar(t->eq.r, x, v));
    case TREFL:
      return Refl(betar(t->refl.a, x, v));
    case TSUCC:
      return Succ (betar (t->succ.p, x, v));
    default:
      return t;
  }
  panic("unreachable");
}

struct term *norm(struct term *t) {
  struct term *f, *a;
  switch (t->tt) {
    case TLAM:
      return Lam(t->l.x, norm(t->l.ty), norm(t->l.b));
    case TAPP:
      f = norm(t->a.lam);
      a = norm(t->a.arg);
      if (f->tt == TLAM)
        return betar(f->l.b, f->l.x, a);
      else
        return App(f, a);
    case TPI:
      return Pi(t->pi.x, norm(t->pi.ta), norm(t->pi.tb));
    case TEQ:
      return Eq(norm(t->eq.ty), norm(t->eq.l), norm(t->eq.r));
    case TREFL:
      return Refl(norm(t->refl.a));
    case TSUCC:
      return Succ (norm (t->succ.p));
    default:
      return t;
  }
  panic("unreachable");
}

bool equal(struct term *t1, struct term *t2) {
  if (!t1 || !t2) {
    panic("null term");
  }
  t1 = norm(t1);
  t2 = norm(t2);
  if (t1->tt != t2->tt)
    return false;
  switch (t1->tt) {
    case TVAR:
      return strcmp(t1->v.n, t2->v.n) == 0;
    case TLAM:
      return equal(t1->l.ty, t2->l.ty) && equal(t1->l.b, betar(t2->l.b, t2->l.x, Var(t1->l.x)));
    case TAPP:
      return equal(t1->a.lam, t2->a.lam) && equal(t1->a.arg, t2->a.arg);
    case TPI:
      return equal(t1->pi.ta, t2->pi.ta) && equal(t1->pi.tb, betar(t2->pi.tb, t2->pi.x, Var(t1->pi.x)));
    case TEQ:
      return equal(t1->eq.ty, t2->eq.ty) && equal(t1->eq.l, t2->eq.l) && equal(t1->eq.r, t2->eq.r);
    case TREFL:
      return equal(t1->refl.a, t2->refl.a);
    case TSUCC:
      return equal (t1->succ.p, t2->succ.p);
    case TTYPE: case TNAT: case TZERO:
      return true;
  }
  panic("unreachable");
}

static int succn (struct term *t, int n) {
  switch (t->tt) {
    case TZERO: return n;
    case TSUCC: return succn (t->succ.p, n + 1);
    default: return -1;
  }
}

static void _dump(struct term *t) {
  int n;
  switch (t->tt) {
    case TTYPE:
      printf("Type");
      break;
    case TVAR:
      printf("%s", t->v.n);
      break;
    case TLAM:
      printf("\\%s: ", t->l.x);
      _dump(t->l.ty);
      printf(" -> ");
      printf("(");
      _dump(t->l.b);
      printf(")");
      break;
    case TAPP:
      printf("(");
      _dump(t->a.lam);
      printf(")");
      printf(" ");
      printf("(");
      _dump(t->a.arg);
      printf(")");
      break;
    case TPI:
      printf("(%s:", t->pi.x);
      _dump(t->pi.ta);
      printf(") -> ");
      _dump(t->pi.tb);
      break;
    case TEQ:
      printf("Eq:");
      _dump(t->eq.ty);
      printf(" (");
      _dump(t->eq.l);
      printf(") (");
      _dump(t->eq.r);
      printf(")");
      break;
    case TREFL:
      printf("Refl ");
      printf("(");
      _dump(t->refl.a);
      printf(")");
      break;
    case TNAT:
      printf ("Nat");
      break;
    case TZERO:
      printf ("Zero");
      break;
    case TSUCC:
      n = succn (t, 0);
      if (n < 0) {
        printf ("Succ ");
        printf ("(");
        _dump (t->succ.p);
        printf (")");
      } else {
        printf ("%d", n);
      }
      break;
    default:
      panic("unreachable");
  }
}

void dump(struct term *t) {
  _dump(t);
  printf("\n");
}

struct term *infer(struct ctx *c, struct term *t) {
  struct term *ty, *tb, *tlam, *ta, *tp;
  switch (t->tt) {
    case TTYPE: case TNAT:
      return Type ();
    case TVAR:
      ty = ctx(c, t->v.n);
      if (ty)
        return ty;
      else
        panic("unbound");
    case TLAM:  /* \x:A -> b */
      if (!equal(infer(c, t->l.ty), Type()))
        panic("Lam mismatch");
      tb = infer(addctx(ccopy(c), t->l.x, t->l.ty), t->l.b);
      return Pi(t->l.x, t->l.ty, tb);
    case TAPP:  /* f arg,  f: (x:A) -> B, arg: A */
      tlam = norm(infer(c, t->a.lam));
      if (tlam->tt == TPI) {
        if (!equal(infer(c, t->a.arg), tlam->pi.ta))
          panic("app mismatch type");
        return betar(tlam->pi.tb, tlam->pi.x, t->a.arg);
      } else {
        panic("non Pi");
      }
    case TPI: /* (x:A) -> B */
      if (!equal(infer(c, t->pi.ta), Type()))
        panic ("Pi type mismatch");
      if (!equal(infer(addctx(ccopy(c), t->pi.x, t->pi.ta), t->pi.tb), Type()))
        panic ("Pi type mismatch");
      return Type ();
    case TEQ:
      if (!equal(infer(c, t->eq.ty), Type()))
        panic ("Eq type mismatch");
      if (!equal(infer(c, t->eq.l), t->eq.ty))
        panic ("Eq.l type mismatch");
      if (!equal(infer(c, t->eq.r), t->eq.ty))
        panic ("Eq.r type mismatch");
      return Type ();
    case TREFL:
      ta = norm (infer(c, t->refl.a));
      return Eq (ta, t->refl.a, t->refl.a);
    case TZERO:
      return Nat ();
    case TSUCC:
      if (!equal (infer (c, t->succ.p), Nat ()))
        panic ("Succ p: type mismatch");
      return Nat ();
  }
  panic ("unreachable");
}


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "term.h"

void proofcheck(struct ctx *c, struct term *theorem, struct term *proof) {
  struct term *ty;
  ty = infer (c, proof);
  if (equal (ty, theorem))
    printf ("proof ok\n");
  else
    printf ("proof failed\n");
}

int main(void) {
  struct ctx *c = malloc(sizeof *c);
  struct term *id, *t, *ty, *n3;
  memset(c, 0, sizeof *c);
  struct term *theorem, *proof;

  // id = \A:Type -> (\x:A -> x)
  id = Lam ("A", Type (), Lam ("x", Var ("A"), Var ("x")));
  dump(id);
  ty = infer(c, id);
  dump(ty);

  addctx (c, "Nat", Type ());   // Nat: Type
  addctx (c, "3", Var ("Nat")); // 3: Nat
  // id Nat 3
  t = App (App (id, Var ("Nat")), Var ("3"));
  dump(infer(c, t));  // Nat
  // (A:Type) -> (x:A) -> Eq A (id A x) x
  theorem = Pi ("A", Type (),
                Pi ("x", Var ("A"), Eq (Var ("A"),
                                        Var ("x"),
                                        App (App (id, Var ("A")), Var ("x"))
                                    )
                )
            );
  // proof: \B:Type -> (\x:B -> Refl x)
  proof = Lam ("B", Type (), Lam ("x", Var ("B"), Refl (Var ("x"))));
  printf("theorem: ");
  dump(theorem);
  printf("proof: ");
  dump(proof);
  proofcheck(c, theorem, proof);

  n3 = Succ (Succ (Succ (Zero ())));
  dump(n3);
}

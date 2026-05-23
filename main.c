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

struct term *nat (unsigned int n) {
  if (n == 0)
    return Zero ();
  return Succ (nat (n - 1));
}

int main(void) {
  struct ctx *c = malloc(sizeof *c);
  struct term *id, *t, *ty, *n1, *n2, *n3, *n4, *n5;
  memset(c, 0, sizeof *c);
  struct term *theorem, *proof;
  struct term *plus, *res;

  // id = \A:Type -> (\x:A -> x)
  id = Lam ("A", Type (), Lam ("x", Var ("A"), Var ("x")));
  dump(id);
  ty = infer(c, id);
  dump(ty);

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

  plus = Lam ("n", Nat (),
              Lam ("m", Nat (),
                   NatRec (
                     Lam ("_", Nat (), Nat ()),
                     Var ("n"),
                     Lam ("_", Nat (), Lam ("r", Nat (), Succ (Var ("r")))),
                     Var ("m")
                   )
              )
         );

  dump (norm (App (App (plus, nat (3)), nat (2))));

  // 2+3 = 1+4
  theorem = Eq (Nat (), App (App (plus, nat (2)), nat (3)), App (App (plus, nat (1)), nat (4)));
  proof = Refl (nat (5));
  printf("theorem: ");
  dump(theorem);
  printf("proof: ");
  dump(proof);
  proofcheck(c, theorem, proof);
}

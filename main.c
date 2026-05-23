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
  struct term *lemma_congS, *congS;
  struct term *lemma_sym, *sym;
  struct term *plus, *res;
  struct term *n_plus_0_is_n;

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

  // plus (n: Nat) -> (m: Nat) -> Nat
  plus = Lam ("n", Nat (),
              Lam ("m", Nat (),
                   NatRec (
                     Lam ("_", Nat (), Nat ()),
                     Var ("m"),
                     Lam ("_", Nat (), Lam ("r", Nat (), Succ (Var ("r")))),
                     Var ("n")
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

  // (a: Nat) -> (b: Nat) -> (Eq Nat a b) -> (Eq Nat (Succ a) (Succ b))
  lemma_congS = Pi ("a", Nat (),
                    Pi ("b", Nat (),
                        Pi ("_", Eq (Nat (), Var ("a"), Var ("b")),
                            Eq (Nat (), Succ (Var ("a")), Succ (Var ("b")))
                        )
                    )
                );
  congS = Lam ("x", Nat (),
               Lam ("y", Nat (),
                    Lam ("p", Eq (Nat (), Var ("x"), Var ("y")),
                         J (Nat (), Var ("x"),
                            Lam ("b'", Nat (), Lam ("_", Eq (Nat (), Var ("x"), Var ("b'")),
                                                    Eq (Nat (), Succ (Var ("x")), Succ (Var ("b'")))
                                               )
                            ),
                            Refl (Succ (Var ("x"))),
                            Var ("y"),
                            Var ("p")
                         )
                    )
               )
          );
  dump (lemma_congS);
  dump (norm (infer (c, congS)));
  proofcheck (c, lemma_congS, congS);
  dump (infer (c, App (App (App (congS, nat (3)), nat (3)), Refl (nat (3)))));
  
  // (A: Type) -> (a: A) -> (b: A) -> (Eq A a b) -> (Eq A b a)
  lemma_sym = Pi ("A", Type (),
                  Pi ("a", Var ("A"),
                      Pi ("b", Var ("A"),
                          Pi ("_", Eq (Var ("A"), Var ("a"), Var ("b")), Eq (Var ("A"), Var ("b"), Var ("a")))
                      )
                  )
              );
  sym = Lam ("T", Type (),
             Lam ("x", Var ("T"),
                  Lam ("y", Var ("T"),
                       Lam ("p", Eq (Var ("T"), Var ("x"), Var ("y")),
                            J (Var ("T"), Var ("x"),
                               Lam ("a'", Var ("T"), Lam ("_", Eq (Var ("T"), Var ("x"), Var ("a'")),
                                                          Eq (Var ("T"), Var ("a'"), Var ("x"))
                                                     )
                               ),
                               Refl (Var ("x")),
                               Var ("y"),
                               Var ("p")
                            )
                       )
                  )
             )
        );
  dump (lemma_sym);
  dump (norm (infer (c, sym)));
  proofcheck (c, lemma_sym, sym);

  // n + 0 = n
  // (n: Nat) -> (Eq Nat (plus n 0) n)
  n_plus_0_is_n = Pi ("n", Nat (), Eq (Nat (), App (App (plus, Var ("n")), nat (0)), Var ("n")));
  proof = Lam ("n", Nat (),
               NatRec (
                 Lam ("x", Nat (), Eq (Nat (), App (App (plus, Var ("x")), nat (0)), Var ("x"))),
                 // zero: 0 + 0 = 0
                 Refl (nat (0)),
                 // succ: k + 0 = k -> (Succ k + 0) = (Succ k)
                 Lam ("k", Nat (),
                      Lam ("ih", Eq (Nat (),
                                     App (App (plus, Var ("k")), nat (0)),
                                     Var ("k")),
                           App (App (App (congS, App (App (plus, Var ("k")), nat (0))), Var ("k")), Var ("ih"))
                      )
                 ),
                 Var ("n")
               )
          );
  dump (n_plus_0_is_n);
  dump (norm (infer (c, proof)));
  proofcheck (c, n_plus_0_is_n, proof);
}

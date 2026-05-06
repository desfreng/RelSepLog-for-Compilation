From stdpp Require Import prelude.

From RSL Require Import Toy.Toy.

Module ToyNotations.
  Declare Custom Entry toy_instr.
  Declare Custom Entry toy_expr.
  Declare Custom Entry toy_reg.

  Notation "<{| e |}>" := e (e custom toy_instr at level 99).

  Notation "r" :=
    (EReg r)
      (in custom toy_expr at level 0,
          r ident).

  Notation "# v" :=
    (EImm v%Z)
      (in custom toy_expr at level 0,
          v constr).

  Notation "'!' addr" :=
    (ELoad addr)
      (in custom toy_expr at level 0,
          addr ident).

  Notation "x '*' y" :=
    (EMul x y)
      (in custom toy_expr at level 0,
          x ident,
          y ident,
          left associativity).

  Notation "x '+' y" :=
    (EAdd x y)
      (in custom toy_expr at level 0,
          x ident,
          y ident,
          left associativity).

  Notation "x '-' y" :=
    (ESub x y)
      (in custom toy_expr at level 0,
          x ident,
          y ident,
          left associativity).

  Notation "'skip'" :=
    ISkip
      (in custom toy_instr).

  Notation "'break' n" :=
    (IBreak n)
      (in custom toy_instr at level 10,
          n constr).

  Notation "'return' v" :=
    (IRet v)
      (in custom toy_instr at level 10,
          v ident).

  Notation "dst ':=' '@' f '(' args ')'" :=
    (ICall dst f args)
      (in custom toy_instr at level 0,
          dst ident,
          f ident,
          args constr).

  Notation "dst ':=' e" :=
    (IAssign dst e)
      (in custom toy_instr at level 0,
          dst ident,
          e custom toy_expr).

  Notation "'*' addr ':=' r" :=
    (IStore addr r)
      (in custom toy_instr at level 70,
          addr ident,
          r ident).

  Notation "'if' cond '{' b1 '}' 'else' '{' b2 '}'" :=
    (IIf cond b1 b2)
      (in custom toy_instr at level 80,
          cond ident,
          b1 custom toy_instr,
          b2 custom toy_instr).

  Notation "'loop' '{' b '}'" :=
    (ILoop b ISkip)
      (in custom toy_instr at level 80,
          b custom toy_instr).

  Notation "'while' cond '{' b '}'" :=
    (IWhile cond b)
      (in custom toy_instr at level 80,
          cond ident,
          b custom toy_instr).

  Notation "'do' '{' b '}' 'while' cond" :=
    (IDoWhile b cond)
      (in custom toy_instr at level 80,
          b ident,
          cond custom toy_reg).

  Notation "s1 ; s2" :=
    (ISeq s1 s2)
      (in custom toy_instr at level 90,
          s1 custom toy_instr,
          s2 custom toy_instr,
          right associativity).

End ToyNotations.

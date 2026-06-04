From RSL Require Import Prelude.
From RSL Require Import Toy.Toy.

Module ToyNotations.
  Declare Custom Entry toy_instr.
  Declare Custom Entry toy_expr.
  Declare Custom Entry toy_reg.

  Notation "<{| e |}>" :=
    e (at level 0, e custom toy_instr at level 99).

  Notation "reg" :=
    (reg%nat)
      (in custom toy_reg at level 0,
          reg ident).

  Notation "r" :=
    (EReg r)
      (in custom toy_expr at level 0,
          r custom toy_reg).

  Notation "# v" :=
    (EImm v%Z)
      (in custom toy_expr at level 1,
          v constr).

  Notation "'!' addr" :=
    (ELoad addr)
      (in custom toy_expr at level 1,
          addr custom toy_reg).

  Notation "x '*' y" :=
    (EMul x y)
      (in custom toy_expr at level 50,
          x custom toy_reg,
          y custom toy_reg).

  Notation "x '+' y" :=
    (EAdd x y)
      (in custom toy_expr at level 50,
          x custom toy_reg,
          y custom toy_reg).

  Notation "x '-' y" :=
    (ESub x y)
      (in custom toy_expr at level 50,
          x custom toy_reg,
          y custom toy_reg).

  #[warning="-closed-notation-not-level-0"]
  Notation "'skip'" :=
    (ISkip)
      (in custom toy_instr at level 10).

  Notation "'break' n" :=
    (IBreak n)
      (in custom toy_instr at level 10,
          n constr).

  Notation "'return' v" :=
    (IRet v)
      (in custom toy_instr at level 10,
          v custom toy_reg).

  #[warning="-postfix-notation-not-level-1"]
  Notation "dst ':=' '@' f '(' args ')'" :=
    (ICall dst f args)
      (in custom toy_instr at level 10,
          dst custom toy_reg,
          f constr at level 0,
          args constr).

  Notation "dst ':=' e" :=
    (IAssign dst e)
      (in custom toy_instr at level 10,
          dst custom toy_reg,
          e custom toy_expr).

  Notation "'*' addr ':=' r" :=
    (IStore addr r)
      (in custom toy_instr at level 10,
          addr custom toy_reg,
          r custom toy_reg).

  #[warning="-closed-notation-not-level-0"]
  Notation "'if' cond '{' b1 '}' 'else' '{' b2 '}'" :=
    (IIf cond b1 b2)
      (in custom toy_instr at level 80,
          cond custom toy_reg,
          b1 custom toy_instr,
          b2 custom toy_instr).

  #[warning="-closed-notation-not-level-0"]
  Notation "'loop' '{' b '}'" :=
    (ILoop b ISkip)
      (in custom toy_instr at level 80,
          b custom toy_instr).

  #[warning="-closed-notation-not-level-0"]
  Notation "'while' cond '{' b '}'" :=
    (IWhile cond b)
      (in custom toy_instr at level 80,
          cond custom toy_reg,
          b custom toy_instr).

  Notation "'do' '{' b '}' 'while' cond" :=
    (IDoWhile b cond)
      (in custom toy_instr at level 80,
          cond custom toy_reg,
          b custom toy_instr).

  Notation "s1 ; s2" :=
    (ISeq s1 s2)
      (in custom toy_instr at level 90,
          s1 custom toy_instr,
          s2 custom toy_instr,
          right associativity).

End ToyNotations.

Section Playground.
  Import ToyNotations.
  Import String.

  Let n : reg := 1.
  Let result : reg := 2.
  Let one : reg := 3.
  Let addr : reg := 4.
  Let fun_name := "toto"%string.

  Definition notation_test : tinstr :=
    <{|
      (* 1. Call *)
      result := @ fun_name ([n]);

      (* 2. Expressions: Immediates and Loads *)
      result := #1;
      one := !addr;

      (* 3. Arithmetic Operations *)
      result := result * result;
      result := result + result;
      result := result - result;

      (* 4. Memory Store *)
      *addr := one;

      (* 5. Control Flow *)
      if one {
          skip
      } else {
          break 0
      };

      while one {
          result := result + n
      };

      loop {
          result := result - one
      };

      do {
          skip
      } while one;

      (* 6. Sequence & Return *)
      return result
    |}>.
End Playground.

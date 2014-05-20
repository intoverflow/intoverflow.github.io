Require Import floyd.proofauto.

Require Import Coq.Strings.Ascii.

Inductive ascii : val -> Prop :=
  | is_ascii c: (0 <= Int.intval c < 128) -> ascii (Vint c).

Inductive ascii_not_nil : val -> Prop :=
  | is_ascii_not_nil c: (0 < Int.intval c < 128) -> ascii_not_nil (Vint c).

Lemma ascii_not_nil_is_ascii: forall v, ascii_not_nil v -> ascii v.
Proof. intros. inversion H. apply is_ascii. omega. Qed.

Inductive ascii_string (contents: Z -> val) (len size: Z) : Prop :=
  | is_ascii_string:
     (0 <= len < size)
     -> (forall i, 0 <= i < len -> ascii_not_nil (contents i))
     -> contents len = Vint Int.zero
     -> ascii_string contents len size.



Require Import strncat.

Local Open Scope logic.

Definition strlen_spec :=
 DECLARE _strlen
  WITH s0: val, sh : share, contents : Z -> val, len: Z, size: Z
  PRE [ _s OF (tptr tuchar) ]
          PROP (0 < size <= Int.max_signed;
                ascii_string contents len size)
          LOCAL (`(eq s0) (eval_id _s); `isptr (eval_id _s))
          SEP (`(array_at tuchar sh contents 0 size) (eval_id _s))
  POST [ tuint ]
        local (`(eq (Vint (Int.repr len))) retval)
              && `(array_at tuchar sh contents 0 size s0).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=  strlen_spec :: nil.
Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma body_strlen: semax_body Vprog Gtot f_strlen strlen_spec.
Proof.
  start_function.
  name s  _s.
  name i  _i.
  name c  _c.
  forward. (* i = 0; *)
  forward. (* c = s[i]; *)
  { entailer!.

  set (strlen_Inv :=
    EX  i : Z,
    PROP  (0 <= i < size)
    LOCAL  (`(eq s0) (eval_id _s); `isptr (eval_id _s);
            `(eq (Vint (Int.repr i))) (eval_id _i))
    SEP  (`(array_at tint sh contents 0 size) (eval_id _s))
    ).
  set (strlen_Post :=
    PROP() LOCAL (`(eq s0) (eval_id _s);
    `(eq (Vint (string_length_int (mk_string contents 0 (nat_of_Z size))))) (eval_id _i))
    SEP (`(array_at tint sh contents 0 size) (eval_id _s))
    ).
  forward_while strlen_Inv strlen_Post ; try (clear strlen_Inv) ; try (clear strlen_Post).
  (* Prove that current precondition implies loop invariant *)
  { apply exp_right with 0.
    entailer!.
  }
  (* Prove that loop invariant implies typechecking condition *)
  { 
  }
  (* Prove that invariant && not loop-cond implies postcondition *)
  {
  }
  (* Prove that loop body preserves invariant *)
  {
  }
Qed.


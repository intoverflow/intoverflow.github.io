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

Lemma ascii_string_is_int:
  forall contents len size,
   ascii_string contents len size
   -> forall i, 0 <= i <= len -> is_int (contents i).
Proof.
  intros.
  destruct (Z_dec i len) eqn:?.
  + destruct s ; try omega.
    destruct H.
    assert (ascii_not_nil (contents i)) as ann by (apply H1 ; omega).
    inversion ann.
    simpl ; trivial.
  + inversion H.
    subst.
    rewrite H3.
    simpl ; trivial.
Qed.


Require Import strncat.

Local Open Scope logic.

Definition strlen_spec :=
 DECLARE _strlen
  WITH s0: val, sh : share, contents : Z -> val, len: Z, size: Z
  PRE [ _s OF (tptr tuchar) ]
          PROP (0 < size <= Int.max_signed;
                ascii_string contents len size)
          LOCAL (`(eq s0) (eval_id _s); `isptr (eval_id _s))
          SEP (`(array_at tuchar sh contents 0 size s0))
  POST [ tuint ]
        local (`(eq (Vint (Int.repr len))) retval)
              && `(array_at tuchar sh contents 0 size s0).

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=  strlen_spec :: nil.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
  start_function.
  set (H_ascii_string := H0).
  destruct H0 as [ zero_lte_len_lt_size H_ascii_not_nil H_contents_len ].
  forward (* i = 0; *).
  forward. (* c = s[i]; *)
  { entailer!.
    destruct (zeq 0 len).
    + subst ; rewrite H_contents_len ; simpl ; trivial.
    + assert (ascii_not_nil (contents 0)) as ann
         by (apply H_ascii_not_nil; omega).
      inv ann; simpl; auto.
  }
  set (strlen_Inv :=
    EX i': Z,
    (PROP ( 0 <= i' <= len )
     LOCAL ( `(eq s0) (eval_id _s)
           ; `(eq (Vint (Int.repr i'))) (eval_id _i)
           ; `(eq (contents i')) (eval_id _c)
           )
     SEP ( `(array_at tuchar sh contents 0 size) (eval_id _s) )
    ) ).
  set (strlen_Post :=
    (PROP ( )
     LOCAL ( `(eq s0) (eval_id _s)
           ; `(eq (Vint (Int.repr len))) (eval_id _i)
           )
     SEP ( `(array_at tuchar sh contents 0 size) (eval_id _s) )
    ) ).
  forward_while strlen_Inv strlen_Post; unfold strlen_Inv, strlen_Post in * ; clear strlen_Inv strlen_Post.
  (* Prove that current precondition implies loop invariant *)
  { apply exp_right with 0.
    entailer!.
    rewrite H0.
    normalize.
    destruct (zeq 0 len).
    + subst ; rewrite H_contents_len ; simpl.
      normalize.
    + assert (ascii_not_nil (contents 0)) as contents_0_ascii_nn.
      { apply H_ascii_not_nil ; omega. }
      assert (is_int (contents 0)) as contents_0_is_int.
      { apply ascii_string_is_int with len size ; try omega.
        apply H_ascii_string.
      }
      destruct (contents 0) ; simpl in contents_0_is_int ; try contradiction.
      destruct contents_0_ascii_nn.
      simpl.
      (* *)
      admit.
  }
  (* Prove that loop invariant implies typechecking condition *)
  { entailer!. }
  (* Prove that invariant && not loop-cond implies postcondition *)
  { entailer!.
    replace len with i' ; trivial.
    apply Z.le_lteq in H1 ; destruct H1 ; try assumption.
    (* now we go for the contradiction *)
    rewrite negb_false_iff in H2.
    apply int_eq_e in H2.
    assert (ascii_not_nil (contents i')) as H_contents_i'.
    { apply H_ascii_not_nil. omega. }
    destruct H_contents_i'.
    inversion H3 ; subst ; simpl in *.
    omega.
  }
  (* Prove that loop body preserves invariant *)
  { forward (* i++; *).
    forward (* c = s[i]; *).
    + entailer!.
      { (* is_int (contents (i' + 1)) *)
        assert (i' < len) as H_i'_len.
        { apply Z.le_lteq in H1 ; destruct H1 ; subst ; try assumption.
          rewrite H_contents_len in H4.
          inversion H4 ; subst.
          compute in H3 ; inversion H3.
        }
        assert (is_int (contents (i' + 1))) as Q.
        { apply ascii_string_is_int with len size.
          + apply H_ascii_string.
          + omega.
        }
        destruct (contents (i' + 1)) ; simpl in * ; try contradiction ; trivial.
      }
      { (* 0 <= i' + 1 < size *)
        assert (i' < len) ; try omega.
        apply Z.le_lteq in H1.
        destruct H1 ; trivial ; subst.
        rewrite H_contents_len in H4 ; inversion H4 ; subst.
        compute in H3 ; inversion H3.
      }
    + entailer!.
      apply exp_right with (i' + 1).
      entailer!.
      { (* i' + 1 <= len *)
        assert (contents i' <> Vint Int.zero).
        { intro Q ; rewrite Q in H4.
          compute in H4 ; inversion H4.
        }
        apply Z.le_lteq in H1.
        destruct H1 ; subst ; try omega ; congruence.
      }
      { (* contents (i' + 1) = Vint _id *)
        rewrite H2 ; normalize.
        (* *)
        admit.
      }
  }
  (* loop is done, continue with rest of proof *)
  forward (* return i; *).
Qed.


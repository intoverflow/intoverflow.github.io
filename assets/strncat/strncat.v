Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _dest : ident := 8%positive.
Definition _i : ident := 5%positive.
Definition _strncat : ident := 12%positive.
Definition _n : ident := 10%positive.
Definition ___builtin_annot_intval : ident := 3%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition _c : ident := 6%positive.
Definition _dest_len : ident := 11%positive.
Definition _s : ident := 4%positive.
Definition _strlen : ident := 7%positive.
Definition _src : ident := 9%positive.
Definition _main : ident := 13%positive.
Definition _dest_len' : ident := 14%positive.


Definition f_strlen := {|
  fn_return := tuint;
  fn_params := ((_s, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_c, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _c
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tuint)
            (tptr tuchar)) tuchar) tuchar))
    (Ssequence
      (Swhile
        (Ebinop One (Econst_int (Int.repr 0) tint) (Etempvar _c tuchar) tint)
        (Ssequence
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          (Sset _c
            (Ecast
              (Ederef
                (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tuint)
                  (tptr tuchar)) tuchar) tuchar))))
      (Sreturn (Some (Etempvar _i tuint))))))
|}.

Definition f_strncat := {|
  fn_return := (tptr tuchar);
  fn_params := ((_dest, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_dest_len, tuint) :: (_i, tuint) :: (15%positive, tint) ::
               (_dest_len', tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _dest_len')
      (Evar _strlen (Tfunction (Tcons (tptr tuchar) Tnil) tuint))
      ((Etempvar _dest (tptr tuchar)) :: nil))
    (Sset _dest_len (Etempvar _dest_len' tuint)))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tuint)
                           tint)
              (Ssequence
                (Sset 15%positive
                  (Ecast
                    (Ebinop One
                      (Ederef
                        (Ebinop Oadd (Etempvar _src (tptr tuchar))
                          (Etempvar _i tuint) (tptr tuchar)) tuchar)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset 15%positive (Ecast (Etempvar 15%positive tbool) tint)))
              (Sset 15%positive (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar 15%positive tint) Sskip Sbreak))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dest (tptr tuchar))
                (Ebinop Oadd (Etempvar _dest_len tuint) (Etempvar _i tuint)
                  tuint) (tptr tuchar)) tuchar)
            (Ederef
              (Ebinop Oadd (Etempvar _src (tptr tuchar)) (Etempvar _i tuint)
                (tptr tuchar)) tuchar)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _dest (tptr tuchar))
            (Ebinop Oadd (Etempvar _dest_len tuint) (Etempvar _i tuint)
              tuint) (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _dest (tptr tuchar)))))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)))
     (Tcons tdouble Tnil) tdouble)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid)) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)))
     (Tcons (tptr tuchar) (Tcons tint Tnil)) tint)) ::
 (_strlen, Gfun(Internal f_strlen)) ::
 (_strncat, Gfun(Internal f_strncat)) :: nil);
prog_main := _main
|}.


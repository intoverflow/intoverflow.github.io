Require Import Clightdefs.

Local Open Scope Z_scope.

Definition ___builtin_fsqrt : ident := 16%positive.
Definition _strlen : ident := 24%positive.
Definition _i : ident := 22%positive.
Definition ___builtin_read16_reversed : ident := 17%positive.
Definition ___builtin_va_end : ident := 8%positive.
Definition ___builtin_va_start : ident := 5%positive.
Definition ___builtin_bswap : ident := 12%positive.
Definition ___compcert_va_int64 : ident := 10%positive.
Definition ___builtin_annot : ident := 3%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition ___builtin_bswap16 : ident := 14%positive.
Definition ___builtin_va_arg : ident := 6%positive.
Definition _src : ident := 26%positive.
Definition ___builtin_write16_reversed : ident := 19%positive.
Definition ___compcert_va_float64 : ident := 11%positive.
Definition ___builtin_annot_intval : ident := 4%positive.
Definition _dest_len : ident := 28%positive.
Definition ___builtin_va_copy : ident := 7%positive.
Definition _s : ident := 21%positive.
Definition ___builtin_read32_reversed : ident := 18%positive.
Definition ___compcert_va_int32 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 13%positive.
Definition _n : ident := 27%positive.
Definition _dest : ident := 25%positive.
Definition ___builtin_cntlz : ident := 15%positive.
Definition _strncat : ident := 29%positive.
Definition _main : ident := 30%positive.
Definition _c : ident := 23%positive.
Definition ___builtin_write32_reversed : ident := 20%positive.
Definition _dest_len' : ident := 31%positive.


Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_c, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _c
      (Ederef
        (Ebinop Oadd (Etempvar _s (tptr tint)) (Etempvar _i tuint)
          (tptr tint)) tint))
    (Ssequence
      (Swhile
        (Ebinop One (Econst_int (Int.repr 0) tint) (Etempvar _c tint) tint)
        (Ssequence
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          (Sset _c
            (Ederef
              (Ebinop Oadd (Etempvar _s (tptr tint)) (Etempvar _i tuint)
                (tptr tint)) tint))))
      (Sreturn (Some (Etempvar _i tuint))))))
|}.

Definition f_strncat := {|
  fn_return := (tptr tint);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tint)) :: (_src, (tptr tint)) :: (_n, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_dest_len, tuint) :: (_i, tuint) :: (32%positive, tint) ::
               (_dest_len', tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _dest_len')
      (Evar _strlen (Tfunction (Tcons (tptr tint) Tnil) tuint cc_default))
      ((Etempvar _dest (tptr tint)) :: nil))
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
                (Sset 32%positive
                  (Ecast
                    (Ebinop One
                      (Ederef
                        (Ebinop Oadd (Etempvar _src (tptr tint))
                          (Etempvar _i tuint) (tptr tint)) tint)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset 32%positive (Ecast (Etempvar 32%positive tbool) tint)))
              (Sset 32%positive (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar 32%positive tint) Sskip Sbreak))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dest (tptr tint))
                (Ebinop Oadd (Etempvar _dest_len tuint) (Etempvar _i tuint)
                  tuint) (tptr tint)) tint)
            (Ederef
              (Ebinop Oadd (Etempvar _src (tptr tint)) (Etempvar _i tuint)
                (tptr tint)) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _dest (tptr tint))
            (Ebinop Oadd (Etempvar _dest_len tuint) (Etempvar _i tuint)
              tuint) (tptr tint)) tint) (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _dest (tptr tint)))))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tuchar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tuchar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_cntlz,
   Gfun(External (EF_builtin ___builtin_cntlz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) :: (_strlen, Gfun(Internal f_strlen)) ::
 (_strncat, Gfun(Internal f_strncat)) :: nil);
prog_main := _main
|}.


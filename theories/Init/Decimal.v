(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decimal numbers *)

(** These numbers coded in base 10 will be used for parsing and printing
    other Rocq numeral datatypes in an human-readable way.
    See the [Number Notation] command.
    We represent numbers in base 10 as lists of decimal digits,
    in big-endian order (most significant digit comes first). *)

Require Import Datatypes Specif.

(** Unsigned integers are just lists of digits.
    For instance, ten is (D1 (D0 Nil)) *)

Inductive uint :=
 | Nil
 | D0 (_:uint)
 | D1 (_:uint)
 | D2 (_:uint)
 | D3 (_:uint)
 | D4 (_:uint)
 | D5 (_:uint)
 | D6 (_:uint)
 | D7 (_:uint)
 | D8 (_:uint)
 | D9 (_:uint).

(** [Nil] is the number terminator. Taken alone, it behaves as zero,
    but rather use [D0 Nil] instead, since this form will be denoted
    as [0], while [Nil] will be printed as [Nil]. *)

Notation zero := (D0 Nil).

(** For signed integers, we use two constructors [Pos] and [Neg]. *)

Variant signed_int := Pos (d:uint) | Neg (d:uint).
Notation int := signed_int.

(** For decimal numbers, we use two constructors [Decimal] and
    [DecimalExp], depending on whether or not they are given with an
    exponent (e.g., 1.02e+01). [i] is the integral part while [f] is
    the fractional part (beware that leading zeroes do matter). *)

Variant decimal :=
 | Decimal (i:int) (f:uint)
 | DecimalExp (i:int) (f:uint) (e:int).

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for decimal.
Notation int_eq_dec := signed_int_eq_dec.
Notation int_beq := signed_int_beq.
Notation internal_int_dec_lb := internal_signed_int_dec_lb.
Notation internal_int_dec_bl := internal_signed_int_dec_bl.

Declare Scope dec_uint_scope.
Delimit Scope dec_uint_scope with uint.
Bind Scope dec_uint_scope with uint.

Declare Scope dec_int_scope.
Delimit Scope dec_int_scope with int.
Bind Scope dec_int_scope with int.

Register uint as num.uint.type.
Register int as num.int.type.
Register decimal as num.decimal.type.

Fixpoint nb_digits d :=
  match d with
  | Nil => O
  | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d =>
    S (nb_digits d)
  end.

(** This representation favors simplicity over canonicity.
    For normalizing numbers, we need to remove head zero digits,
    and choose our canonical representation of 0 (here [D0 Nil]
    for unsigned numbers and [Pos (D0 Nil)] for signed numbers). *)

(** [nzhead] removes all head zero digits *)

Fixpoint nzhead d :=
  match d with
  | D0 d => nzhead d
  | _ => d
  end.

(** [unorm] : normalization of unsigned integers *)

Definition unorm d :=
  match nzhead d with
  | Nil => zero
  | d => d
  end.

(** [norm] : normalization of signed integers *)

Definition norm d :=
  match d with
  | Pos d => Pos (unorm d)
  | Neg d =>
    match nzhead d with
    | Nil => Pos zero
    | d => Neg d
    end
  end.

(** A few easy operations. For more advanced computations, use the conversions
    with other Rocq numeral datatypes (e.g. Z) and the operations on them. *)

Definition opp (d:int) :=
  match d with
  | Pos d => Neg d
  | Neg d => Pos d
  end.

Definition abs (d:int) : uint :=
  match d with
  | Pos d => d
  | Neg d => d
  end.

(** For conversions with binary numbers, it is easier to operate
    on little-endian numbers. *)

Fixpoint revapp (d d' : uint) :=
  match d with
  | Nil => d'
  | D0 d => revapp d (D0 d')
  | D1 d => revapp d (D1 d')
  | D2 d => revapp d (D2 d')
  | D3 d => revapp d (D3 d')
  | D4 d => revapp d (D4 d')
  | D5 d => revapp d (D5 d')
  | D6 d => revapp d (D6 d')
  | D7 d => revapp d (D7 d')
  | D8 d => revapp d (D8 d')
  | D9 d => revapp d (D9 d')
  end.

Definition rev d := revapp d Nil.

Definition app d d' := revapp (rev d) d'.

Definition app_int d1 d2 :=
  match d1 with Pos d1 => Pos (app d1 d2) | Neg d1 => Neg (app d1 d2) end.

(** [nztail] removes all trailing zero digits and return both the
    result and the number of removed digits. *)

Definition nztail d :=
  let fix aux d_rev :=
    match d_rev with
    | D0 d_rev => let (r, n) := aux d_rev in pair r (S n)
    | _ => pair d_rev O
    end in
  let (r, n) := aux (rev d) in pair (rev r) n.

Definition nztail_int d :=
  match d with
  | Pos d => let (r, n) := nztail d in pair (Pos r) n
  | Neg d => let (r, n) := nztail d in pair (Neg r) n
  end.

(** [del_head n d] removes [n] digits at beginning of [d]
    or returns [zero] if [d] has less than [n] digits. *)

Fixpoint del_head n d :=
  match n with
  | O => d
  | S n =>
    match d with
    | Nil => zero
    | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d =>
      del_head n d
    end
  end.

Definition del_head_int n d :=
  match d with
  | Pos d => del_head n d
  | Neg d => del_head n d
  end.

(** [del_tail n d] removes [n] digits at end of [d]
    or returns [zero] if [d] has less than [n] digits. *)

Definition del_tail n d := rev (del_head n (rev d)).

Definition del_tail_int n d :=
  match d with
  | Pos d => Pos (del_tail n d)
  | Neg d => Neg (del_tail n d)
  end.

Module Little.

(** Successor of little-endian numbers *)

Fixpoint succ d :=
  match d with
  | Nil => D1 Nil
  | D0 d => D1 d
  | D1 d => D2 d
  | D2 d => D3 d
  | D3 d => D4 d
  | D4 d => D5 d
  | D5 d => D6 d
  | D6 d => D7 d
  | D7 d => D8 d
  | D8 d => D9 d
  | D9 d => D0 (succ d)
  end.

(** Doubling little-endian numbers *)

Fixpoint double d :=
  match d with
  | Nil => Nil
  | D0 d => D0 (double d)
  | D1 d => D2 (double d)
  | D2 d => D4 (double d)
  | D3 d => D6 (double d)
  | D4 d => D8 (double d)
  | D5 d => D0 (succ_double d)
  | D6 d => D2 (succ_double d)
  | D7 d => D4 (succ_double d)
  | D8 d => D6 (succ_double d)
  | D9 d => D8 (succ_double d)
  end

with succ_double d :=
  match d with
  | Nil => D1 Nil
  | D0 d => D1 (double d)
  | D1 d => D3 (double d)
  | D2 d => D5 (double d)
  | D3 d => D7 (double d)
  | D4 d => D9 (double d)
  | D5 d => D1 (succ_double d)
  | D6 d => D3 (succ_double d)
  | D7 d => D5 (succ_double d)
  | D8 d => D7 (succ_double d)
  | D9 d => D9 (succ_double d)
  end.

End Little.

(** Pseudo-conversion functions used when declaring
    Number Notations on [uint] and [int]. *)

Definition uint_of_uint (i:uint) := i.
Definition int_of_int (i:int) := i.

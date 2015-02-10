Require Import Arith Omega.
Require Import List.
Require Import Sorted.

Definition P {A} (u v : list A) := exists x, In x u /\ In x v.

Definition Spec (f : list nat -> list nat -> bool) := forall u v, StronglySorted (lt) u -> StronglySorted (lt) v -> if f u v then P u v else ~ P u v.

Definition Spec' (f : list nat * list nat -> bool) := forall uv, StronglySorted (lt) (fst uv) -> StronglySorted (lt) (snd uv) -> if f uv then P (fst uv) (snd uv) else ~ P (fst uv) (snd uv).

Require Import Recdef.

Definition totallen (uv : list nat * list nat) := length (fst uv) + length (snd uv).

Function intp (uv : list nat * list nat) {measure totallen} : bool :=
  match fst uv with
    | nil => false
    | x :: xs =>
      match snd uv with
        | nil => false
        | y :: ys =>
          match lt_eq_lt_dec x y with
            | inleft (left _) (* x < y *) => intp (xs, y :: ys)
            | inleft (right _) (* x = y *) => true
            | inright _ (* x > y *) => intp (x :: xs, ys)
          end
      end
  end.

unfold totallen; intros; destruct uv; simpl in *; subst; simpl.
omega.

unfold totallen; intros; destruct uv; simpl in *; subst; simpl.
omega.
Defined.

Check (intp_ind (fun uv b => if b then P (fst uv) (snd uv) else ~ P (fst uv) (snd uv))).


Lemma not_P_nil {A} (v : list A) : ~ P nil v.
Proof.
  unfold P; intros [x [l r]].
  inversion l.
Qed.

Lemma not_P_nil2 {A} (v : list A) : ~ P v nil.
Proof.
  unfold P; intros [x [l r]].
  inversion r.
Qed.

Lemma P_head {A} (v : A) (us vs : list A) : P (v :: us) (v :: vs).
Proof.
  exists v; split; constructor; reflexivity.
Qed.

Lemma In_lemma (x a0 : nat) (v : list nat) :
  StronglySorted lt (a0 :: v) ->
  x < a0 ->
  ~In x (a0 :: v).
Proof.
  intros S l I.
  inversion I; subst.
  omega.
  destruct v.
  inversion H.
  inversion S; subst.
  destruct (Forall_forall (lt a0) (n :: v)) as [Lemma _].
  pose (Lemma H3 x H).
  omega.
Qed.

Theorem intp_Spec : Spec' intp.
Proof.
  unfold Spec'.

  intros uv.

  apply (intp_ind (fun uv b => StronglySorted lt (fst uv) -> StronglySorted lt (snd uv) -> if b then P (fst uv) (snd uv) else ~ P (fst uv) (snd uv))); simpl; intros;
  repeat match goal with
           | [ uv : (?a * ?b)%type |- _ ] => destruct uv
         end; simpl in *; subst.
  
  apply not_P_nil.

  apply not_P_nil2.
  
  unfold P in *.
  destruct (intp (xs, y :: ys)).
  Focus 1.
  assert (StronglySorted lt xs) as H2.
  inversion H0; assumption.
  destruct (H H2 H1) as [x' [L R]].
  exists x'; split.
  right; assumption.
  assumption.
  Focus 1.
  assert (StronglySorted lt xs) as H2.
  inversion H0; assumption.
  intro H3; apply (H H2 H1); clear H.
  destruct H3 as [x' [L R]].
  inversion L; subst.
  pose (In_lemma _ _ _ H1 _x R) as f.
  elim f.
  exists x'; split; assumption.

  unfold P in *.
  exists y; split; constructor; reflexivity.
  
  unfold P in *.
  destruct (intp (x :: xs, ys)).
  Focus 1.
  assert (StronglySorted lt ys) as H2.
  inversion H1; assumption.
  destruct (H H0 H2) as [x' [L R]].
  exists x'; split.
  assumption.
  right; assumption.
  Focus 1.
  assert (StronglySorted lt ys) as H2.
  inversion H1; assumption.
  intro H3; apply (H H0 H2); clear H.
  destruct H3 as [x' [L R]].
  inversion R; subst.
  pose (In_lemma _ _ _ H0 _x L) as f.
  elim f.
  exists x'; split; assumption.
Qed.

Extraction Language Ocaml.

Extraction intp.

(****

(** val intp : (nat list, nat list) prod -> bool **)

let rec intp uv =
  match fst uv with
  | Nil -> False
  | Cons (x, xs) ->
    (match snd uv with
     | Nil -> False
     | Cons (y, ys) ->
       (match lt_eq_lt_dec x y with
        | Inleft s ->
          (match s with
           | Left -> intp (Pair (xs, (Cons (y, ys))))
           | Right -> True)
        | Inright -> intp (Pair ((Cons (x, xs)), ys))))


 ***)

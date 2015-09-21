(* begin hide *)
Require Import BinPos.
Require Import ZArith.
Require Import Relations.
Open Scope positive_scope.

(* This has been removed from the Coq library since this was originally written *)
Lemma ZL11 : forall p:positive, p = xH \/ p <> xH.
Proof.
intros x; case x; intros; (left; reflexivity) || (right; discriminate).
Qed.
(* end hide *)

(** In high school, we all learn algebraic rules for
    simplifying expressions. The following eleven identities over the
    positive integers cover most of the cases we encounter in school:

    - #\(x + y = y + x\)#
    - #\((x + y) + z = x + (y + z)\)#
    - #\(x \cdot 1 = x \)#
    - #\(x \cdot y = y \cdot x \)#
    - #\((x \cdot y) \cdot z = x \cdot (y \cdot z)\)#
    - #\(1^x = 1\)#
    - #\(x^1 = x\)#
    - #\(x^{y+z} = x^y \cdot x^z\)#
    - #\((x \cdot y)^z = x^z \cdot y^z\)#
    - #\((x^y)^z = x^{y \cdot z}\)#

    One question that arises is whether these rules are
    _complete_. That is, can we prove every valid identity over the
    positive integers holds just using these eleven rules?

    This problem is known as #<a href="http://en.wikipedia.org/wiki/Tarski's_high_school_algebra_problem">Tarski's high school algebra
    problem</a>#. The Wikipedia page gives a good summary of the problem,
    its solution, and related work. In short, the answer is _no_.
    Andrew Wilkie proved this by giving an equation:
   
    #\[\begin{equation}
      \begin{split}
      {\left( (1 + x)^y + (1 + x + x^2)^y\right)^x \cdot
      \left((1 + x^3)^x + (1 + x^2 + x^4)^x\right)^y} \\

      = {\left((1 + x)^x + (1 + x + x^2)^x\right)^y \cdot
      \left((1 + x^3)^y + (1 + x^2 + x^4)^y\right)^x}
      \end{split}
      \end{equation}\]#
   
    that is true for all positive integers #\(x\)# and #\(y\)#.  He
    then showed that it is not possible to give a proof of this
    equation just using the eleven rewrite rules above.

    In this post, I will give a mechanized proof of Wilkie's theorem
    in the _Coq_ proof assistant.  However, I will formalize a proof
    due to Burris and Yeats instead of Wilkie's original proof.

    We begin by defining the algebraic expressions we are talking about
    as a _Coq_ data type:
    
*)

Inductive expression : Set :=
  | Var: nat -> expression
  | Const: positive -> expression
  | Eplus : expression -> expression -> expression
  | Etimes: expression -> expression -> expression 
  | Epow: expression -> expression -> expression.

(** Instead of representing variables by letters like "x" and "y", we
    will index them using natural numbers. [Var 0] will be the first
    variable, [Var 1] will be the second, and so on. We also define
    some notation to make it easier to write and read these
    expressions. *)

Infix "+" := Eplus : expression_scope.
Infix "*" := Etimes : expression_scope.
Infix "^" := Epow : expression_scope.

(** Next, we would like to give a _denotation_ to these algebraic
    expressions.  What we mean here is, when we have an expression
    like:
    
    #\[ x^2 + x + 4 \]#
   
    We can think of this as the description of a function from
    positive integers (which will be bound to the variable #\(x\)#) to
    positive integers. We would like to capture this idea formally.

    Unfortunately, we first need to define exponentiation on the
    positive integers.  Although the _Coq_ standard library has
    definitions for exponentiation over general integers and natural
    numbers, I did not find one for the positive integer type. This is
    easy enough to do ourselves.  This definition is just like Zpower
    from the standard library, but uses iter_pos instead of
    iter_nat *)

Definition Ppower (x y: positive) := 
  iter_pos y positive (fun q: positive => x * q) 1.
Infix "^" := Ppower : positive_scope.

(** We also prove some lemmas about this operation. The proofs are
    omitted here, but they can be found in the full source file *)

Lemma unit_power: forall x, 1^x = 1.
(* begin hide *) 
Proof.
  apply Pind. auto.
  intros. unfold Ppower in *. rewrite iter_nat_of_P in *. simpl.
  rewrite nat_of_P_succ_morphism. auto.
Qed.

Definition Ppower_nat (x: positive) (n: nat) := 
  iter_nat n positive (fun q: positive => x * q) 1.

(*end hide *)
Lemma exp_one: forall x, x^1 = x.
(* begin hide *) 
Proof.
  intros; unfold Ppower; simpl; apply Pmult_1_r.
Qed.

(*end hide *)
Lemma exp_plus_aux: forall y z x, 
  Ppower_nat x (y + z) = Ppower_nat x y * Ppower_nat x z.
(* begin hide *) 
Proof.
  induction y; intros. auto. 
  simpl in *. unfold Ppower_nat in *. simpl in *. rewrite IHy. 
  apply Pmult_assoc. 
Qed.

Lemma Ppower_conv_Ppower_nat: 
  forall x y, Ppower x y = Ppower_nat x (nat_of_P y).
Proof.
  intros; unfold Ppower, Ppower_nat; 
    rewrite iter_nat_of_P in *; auto.
Qed.

(*end hide *)
Lemma exp_plus: forall x y z, x ^ (y + z) = x^y * x^z.
(* begin hide *) 
Proof.
  intros. repeat rewrite Ppower_conv_Ppower_nat.
  rewrite nat_of_P_plus_morphism. 
  apply exp_plus_aux.
Qed.

(*end hide *)
Lemma exp_mult: forall z x y, (x * y) ^ z = x^z * y^z.
(* begin hide *) 
Proof.
  apply (Pind (fun z => forall x y, (x * y) ^ z = x^z * y^z)).
  intros; simpl. repeat rewrite exp_one; auto.
  intros; simpl. assert (Psucc p = 1 + p). destruct p; auto.
  rewrite H0. repeat rewrite exp_plus.
  repeat rewrite exp_one.
  rewrite (H x y).
  symmetry.
  rewrite Pmult_assoc.
  rewrite <-(Pmult_assoc x (x ^ p) y).
  rewrite (Pmult_comm (x^p) y).
  rewrite Pmult_assoc.
  rewrite Pmult_assoc.
  auto.
Qed.

(*end hide *)
Lemma exp_exp: forall z x y, (x ^ y) ^ z = x ^ (y * z).
(* begin hide *) 
Proof.
  apply (Pind (fun z => forall x y, (x ^ y) ^ z = x ^ (y * z))). 
  intros. rewrite exp_one. rewrite Pmult_1_r. auto.
  intros. assert (Psucc p = 1 + p). destruct p; auto.
  rewrite H0.
  rewrite exp_plus.
  rewrite Pmult_plus_distr_l.
  rewrite exp_plus.
  rewrite exp_one.
  rewrite Pmult_1_r.
  rewrite (H x y). auto. 
Qed.

(*end hide *)


(** Since all of the other operators we need are in the standard library, 
    we are ready to define the denotation of algebraic expressions: *)

Fixpoint denote (e: expression) (f: nat -> positive) : positive :=
  match e with
    | Var n => f n
    | Const n => n
    | Eplus e1 e2 => denote e1 f + denote e2 f
    | Etimes e1 e2 => denote e1 f * denote e2 f
    | Epow e1 e2 => denote e1 f ^ denote e2 f
  end.

(** Given an expression [e] and a function [f] from [nat -> positive],
    denote uses the function [f] as map to look up the values of the
    variables in the expression. That is, [Var n] gets mapped to [f
    n]. Constant terms are mapped to the corresponding [positive], and
    [Eplus], [Etimes], and [Epow] are mapped to the corresponding
    operator for the [positive] type.

    Now we give an inductive data type corresponding to proofs using
    the eleven high school identities:*)

Local Open Scope expression_scope.

Inductive td : expression -> expression -> Prop :=
  | plus: forall x x' y y', td x x' -> td y y' -> td (x + y) (x' + y')
  | times: forall x x' y y', td x x' -> td y y' -> td (x * y) (x' * y')
  | pow: forall x x' y y', td x x' -> td y y' -> td (x ^ y) (x' ^ y')
  | cplus: forall p1 p2, td (Const p1 + Const p2) (Const (p1 + p2))
  | ctimes: forall p1 p2, td (Const p1 * Const p2) (Const (p1 * p2))
  | cpow: forall p1 p2, td (Const p1 ^ Const p2) (Const (p1 ^ p2))
  | refl: forall x, td x x
  | trans: forall x y z, td x y -> td y z -> td x z
  | sym: forall x y, td x y -> td y x
  | t1: forall x y, td (x + y) (y + x)
  | t2: forall x y z, td ((x + y) + z) (x + (y + z))
  | t3: forall x, td (x * (Const 1)) x
  | t4: forall x y, td (x * y) (y * x)
  | t5: forall x y z, td ((x * y) * z) (x * (y * z))
  | t6: forall x y z, td (x * (y + z)) (x * y + x * z)
  | t7: forall x, td ((Const 1) ^ x) (Const 1)
  | t8: forall x, td (x^(Const 1)) x
  | t9: forall x y z, td (x^(y + z)) (x^y * x^z)
  | t10: forall x y z, td ((x * y)^z) (x^z * y^z)
  | t11: forall x y z, td ((x^y) ^ z) (x^(y * z)).

(** Given two expression [e1] and [e2], if we can build a term of type
    [td e1 e2] then there is a proof that [e1 = e2] using one of the
    eleven identities. The constructors [t1] through [t11] correspond
    to these identities, but we also have some extras. [plus],
    [times], and [pow] state that if we have a proof that e1 and e1'
    are equal, and e2 and e2' are equal then e1 + e2 is equal to e1' +
    e2', and e1 * e2 is equal to e1' * e2', etc. [cplus], [ctimes],
    and [cpow] let us fold constants so that we can conclude td (Const
    1 + Const 1) (Const 2)

    Then we have [refl], [sym] and [trans] which correspond to the
    idea that e1 is always equal to itself, if e1 equals e2 then e2
    equals e1, and that if we have a proof that e1 is equal to e2, and
    e2 is equal to e3, then we also have a proof that e1 is equal to
    e3. *)

(** We also establish notation. We use [[=]] instead of "=" because this
    equality is distinct from the built-in equality in _Coq_ *)

Infix "[=]" := td (at level 70) : expression_scope.

(** Now we can prove that these rules are sound. That is, if we can
    construct a proof that [e1 [=] e2], then for each possible
    denotation of [e1] and [e2], the resulting values are equal. *)

Lemma td_sound: forall x y, x [=] y -> forall f, denote x f = denote y f.
Proof.
  intros.
  induction H; simpl; auto.
  rewrite IHtd1; rewrite IHtd2; auto with *.
  rewrite IHtd1; rewrite IHtd2; auto with *.
  rewrite IHtd1; rewrite IHtd2; auto with *.
  rewrite IHtd1; rewrite IHtd2; auto with *.
  apply Pplus_comm.
  rewrite Pplus_assoc; auto.
  apply Pmult_1_r.
  apply Pmult_comm.
  rewrite Pmult_assoc; auto.
  apply Pmult_plus_distr_l.
  apply unit_power.
  apply exp_one.
  apply exp_plus.
  apply exp_mult.
  apply exp_exp.
Qed.

(** Now we can prove identities in _Coq_ about positive integers by
    constructing corresponding [expressions], say e1 and e2, building
    a term of the type td e1 e2, and then using the previous lemma.

    In practice, we don't really want to be doing this. Proving the
    following fact "directly" using the usual _Coq_ tactics is a lot
    more pleasant and efficient, this is just merely to demonstrate
    that it can be done. *)
    
Remark example:
  (forall x y, (x + y) * (x + y) = x ^ 2 + 2 * (x * y) + y ^2)%positive.
Proof.
  intros.
  pose (e1 := (Var 0 + Var 1) * (Var 0 + Var 1)).
  pose (e2 := (Var 0) ^ (Const 2) + (Const 2) * (Var 0 * Var 1) + 
    (Var 1) ^ (Const 2)).
  pose (f := fun (n:nat) => match n with O => x | _ => y end).
  specialize (td_sound e1 e2). intros.
  pose (e1' := (Var 0 + Var 1) * (Var 0) + (Var 0 + Var 1) * Var 1).
  pose (e1'' := (Var 0 * Var 0) + (Var 1 * Var 0) + (Var 0 + Var 1) 
    * Var 1).
  assert (e1 [=] e2).
  eapply trans.
    eapply t6.
  eapply trans.
  eapply plus.

  (** I will omit the rest of this proof since it's quite tedious *)

  (* begin hide *)
    eapply t4.
    eapply t4.
  eapply trans.
  eapply plus.
    eapply t6.
    eapply t6.
  eapply sym.
  eapply trans.
  eapply plus.
  eapply plus.
  eapply pow.
  eapply refl.
  eapply sym.
  eapply cplus with (p1 := 1) (p2 := 1).
  eapply refl.
  eapply pow.
  eapply refl.
  eapply sym.
  eapply cplus with (p1 := 1) (p2 := 1).
  eapply trans.
  eapply plus.
  eapply plus.
  eapply trans.
  eapply t9.
  eapply trans.
  eapply times.
  eapply t8.
  eapply t8.
  eapply refl.
  eapply trans.
  eapply times.
  eapply sym. eapply cplus with (p1 := 1) (p2 := 1).
  eapply refl.
  eapply trans.
  eapply t4.
  eapply trans.
  eapply t6.
  eapply plus.
  eapply t3.
  eapply t3.
  eapply trans.
  eapply t9.
  eapply times.
  eapply t8.
  eapply t8.
  eapply trans.
  eapply t2.
  eapply sym.
  eapply trans.
  eapply t2.
  eapply plus.
  eapply refl.
  eapply trans.
  eapply sym.
  eapply t2.
  eapply plus.
  eapply plus. eapply refl.
  eapply t4.
  eapply refl.
  (* end hide *)
  specialize (H H0 f).
  simpl in H. auto.
Qed.

(** Now, what we'd like to prove is that there is some pair of
    expressions [e1] and [e2] such that [forall f, denote e1 f =
    denote e2 f] (which implies that they correspond to a valid
    identity over the positive integers) but for which there does not
    exist a term of type td e1 e2 (ie we cannot prove the identity
    using the high school identities

    We begin by constructing [expression] terms [w1] and [w2]
    corresponding to Wilkie's counterexample. *)

Definition w1 := 
  (((Const 1) + (Var 0))^(Var 1) + 
   ((Const 1) + (Var 0) + (Var 0)^(Const 2))^(Var 1))^(Var 0) *
  (((Const 1 + (Var 0)^(Const 3))^(Var 0)) +
   ((Const 1 + (Var 0)^(Const 2) + (Var 0)^(Const 4))^(Var 0)))^(Var 1). 

Definition w2 := 
  (((Const 1) + (Var 0))^(Var 0) +
   ((Const 1) + (Var 0) + (Var 0)^(Const 2))^(Var 0))^(Var 1) *
  (((Const 1) + (Var 0)^(Const 3))^(Var 1) +
   ((Const 1) + (Var 0)^(Const 2) + (Var 0)^(Const 4))^(Var 1))^(Var 0).

(** We'll now want to prove that [forall f, denote w1 f = denote w2
    f]. Let's first talk about how this proof would proceed on paper.
    In Wilkie's original paper he lets #\(A = 1 + x\), \(B = 1 + x +
    x^2 \), \(C = 1 + x^3\) and \(D = 1 + x^2 + x^4\)#, so that the
    left hand side of his counterexample becomes #\( (A^x + B^x)^y(C^y
    + d^y)^x\)# and the right hand side becomes #\( (A^y + B^y)^x (C^x
    + D^x)^y \)#.
   
    Then by observing that #\(C = A \cdot (1 + x + x^2) \)# and 
    #\(D = B \cdot (1 + x + x^2)\)#, we can factor out 
    #\((1 + x + x^2)^{xy}\)# from both sides and then the equality
    of the two expressions is clear.

    To do this in Coq we first construct a function [denote_z] that
    instead of mapping our [expressions] onto positives, will instead
    map them onto integers *)

Fixpoint denote_z (e: expression) (f: nat -> positive) : Z :=
  (match e with
    | Var n => Zpos (f n)
    | Const n => Zpos n
    | Eplus e1 e2 => denote_z e1 f + denote_z e2 f
    | Etimes e1 e2 => denote_z e1 f * denote_z e2 f
    | Epow e1 e2 => denote_z e1 f ^ denote_z e2 f
  end)%Z.

(** The reason for doing this is that our proof will involve factoring
    out terms of the form #\([1 - x + x^2\)#.  This term involves
    subtraction. However, the positives are not closed under
    subtraction. The definition for subtraction in _Coq's_ standard
    library deals with this by defining [x - y] to be [1] if [y >= x].

    Obviously, such a definition of subtraction does not have the
    properties we usually expect. By mapping things onto
    [Z] instead, we will work in an expanded domain where intermediary
    values can be negative, even though the final expression will
    still evaluate to a positive number. 

    We first quickly prove an intermediate result we need*)

Require Import Zpow_facts.
Lemma zpow_pos: forall p1 p2, (Zpos p1 ^ Zpos p2 = Zpos (p1 ^ p2))%Z.
(* begin hide *)
Proof.
  intro; apply Pind.
  rewrite exp_one. simpl. apply Zpower_pos_1_r.
  intros.
  assert (Zpos (Psucc p) = Zpos p + 1)%Z. 
  rewrite Pplus_one_succ_r. auto with *.
  rewrite H0.
  rewrite Pplus_one_succ_r. 
  rewrite exp_plus.
  rewrite Zpower_exp; auto with *.
  rewrite H. auto with *.
  apply Zle_ge.
  apply Zlt_le_weak.
  apply Zgt_lt.
  auto with *.
Qed.
(* end hide *)

(** The next two lemmas capture the idea that if we prove an 
    identity is valid using our expanded domain of [Z],
    it will still hold under our normal definition of [denote] *)

Lemma denote_to_denotez: forall e f, denote_z e f = Zpos (denote e f).
Proof.
 induction e; simpl; auto;
 intros;
 try (specialize (IHe1 f); specialize (IHe2 f); 
   rewrite IHe1; rewrite IHe2; auto).
 apply zpow_pos. 
Qed.

Lemma denote_z_implies_denote: 
  forall e1 e2, (forall f, denote_z e1 f = denote_z e2 f) 
    -> (forall f, denote e1 f = denote e2 f).
Proof.
  intros. 
  specialize (denote_to_denotez e1 f).
  specialize (denote_to_denotez e2 f).
  intros.
  specialize (H f).
  rewrite H0 in H.
  rewrite H1 in H.
  inversion H.
  auto.
Qed.

(** Now we are ready to prove that [w1 = w2] is a valid identity
    using our usual [denote function]. This proof is a little  
    long, and it's probably not good _Coq_ style, but I have
    tried to structure it according to the factorization suggested
    by Wilkie in his initial paper. *)

Local Open Scope Z_scope.

Lemma Zexp_exp: 
  forall p2 x p1, (x ^ (Zpos p1)) ^ (Zpos p2) = x ^ (Zpos p1 * Zpos p2).
(* begin hide *)
Proof.
  apply (Pind (fun z => 
    forall x y, (x ^ (Zpos y)) ^ (Zpos z) = x ^ ((Zpos y) * (Zpos z)))). 
  intros.
  unfold Zpower.
  rewrite Zpower_pos_1_r.  
  rewrite Zmult_1_r. auto.
  intros.
  assert (Psucc p = 1 + p)%positive. destruct p; auto.
  rewrite H0.
  assert (x ^ (Zpos y * Zpos (1 + p)) = x ^ (Zpos y) * x ^ (Zpos (y * p))).
  unfold Zpower.
  assert (Zpos y * Zpos (1 + p) = Zpos (y * (1 + p))) by auto with *.
  rewrite H1.
  rewrite Pmult_plus_distr_l.
  rewrite Pmult_1_r.
  auto with *.
  rewrite H1.  
  unfold Zpower.
  rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r.
  unfold Zpower in H.
  rewrite H.
  auto with *.
Qed.
(* end hide *)
Lemma Zpower_pos_mult: 
  forall x y p, (x * y) ^ (Zpos p) = x^(Zpos p) * y^(Zpos p).
(* begin hide *)
Proof.
  intros.
  apply Zmult_power. 
  auto with *.
Qed.
(* end hide *)

Lemma w1_eq_w2: forall f, denote w1 f = denote w2 f.
Proof.
  apply denote_z_implies_denote.
  intros. unfold w1. unfold w2. 
  unfold denote_z.
  pose (x := Zpos (f 0%nat)).
  pose (y := Zpos (f 1%nat)).
  fold x. fold y.
  pose (A := 1 + x).
  pose (B := 1 + x + x^2).
  pose (C := 1 + x^3).
  pose (D := 1 + x^2 + x^4).
  fold B. fold A.
  fold C. fold D.
  assert (C = A * (1 - x + x^2)).
    unfold C. unfold A.
    ring.
  assert (D = B * (1 - x + x^2)). 
    unfold D. unfold B.
    ring.
  assert ((C ^ x + D ^ x) ^ y = (1 - x + x^2)^(x * y) * (A ^ x + B ^x)^y).
    rewrite H. rewrite H0.
    unfold x, y.
    rewrite Zpower_pos_mult.
    rewrite Zpower_pos_mult.
    fold x. fold y.
    rewrite <-Zmult_plus_distr_l.
    unfold y.
    rewrite Zpower_pos_mult.
    fold y.
    unfold x, y.
    rewrite Zexp_exp. 
    fold x. fold y.
    ring.
  rewrite H1.  
  assert ((C ^ y + D ^ y) ^ x = (1 - x + x^2)^(x * y) * (A ^ y + B ^y)^x).
    rewrite H. rewrite H0.
    unfold x, y.
    rewrite Zpower_pos_mult.
    rewrite Zpower_pos_mult.
    fold x. fold y.
    rewrite <-Zmult_plus_distr_l.
    unfold x.
    rewrite Zpower_pos_mult.
    fold x.
    unfold x, y.
    rewrite Zexp_exp. 
    fold x. fold y.
    replace (y * x) with (x * y) by (auto with * ). 
    ring.
  rewrite H2.
  ring.
Qed.

(** We must now prove that [~ td w1 w2]. This is the critical step of
    the proof. How can we possibly prove that there does not exist a
    proof using these rules? Following the proof from Burris and
    Yeats, we define an algebra of 12 elements along with definitions
    of [+], [*], and [^] on this algebra.

    Then we'll show that this algebra satisfies all of the eleven high
    school identities. We'll also show that [w1 = w2] is _not_ a valid
    identity over this 12 element algebra, by explicitly picking
    values for the variables at which the two expressions differ.

    This will show that there cannot be a proof of w1 = w2
    using the high school identities, because if there were that would
    mean that the equation w1 = w2 would also hold over the 12 element
    algebra.
  
    We start by defining the algebra. We omit the definitions of
    addition, multiplication, and exponentiation on this algebra
    since they are just long match statements that elucidate
    little. This algebra was discovered by Burris and Yeats through
    the use of a computer program, so it is not very "natural". *)

Inductive byalg :=
  | n1 | n2 | n3 | n4
  | a  | b  | c  | d
  | e  | f  | g  | h.

(* begin hide *)
Definition byplus b1 b2 :=
  match (b1, b2) with
    | (n1, n1) => n2
    | (n1, n2) => n3
    | (n1, n3) => n4
    | (n1, n4) => n4
    | (n1, a) => n2
    | (n1, b) => n3
    | (n1, c) => d
    | (n1, d) => n3
    | (n1, e) => n3
    | (n1, f) => n3
    | (n1, g) => n3
    | (n1, h) => n4
    (* n2 + _*)
    | (n2, n1) => n3
    | (n2, n2) => n4
    | (n2, n3) => n4
    | (n2, n4) => n4
    | (n2, a) => n3
    | (n2, b) => n4
    | (n2, c) => n3
    | (n2, d) => n4
    | (n2, e) => n4
    | (n2, f) => n4
    | (n2, g) => n4
    | (n2, h) => n4
    (* n3 + _ *)
    | (n3, n1) => n4
    | (n3, n2) => n4
    | (n3, n3) => n4
    | (n3, n4) => n4
    | (n3, a) => n4
    | (n3, b) => n4
    | (n3, c) => n4
    | (n3, d) => n4
    | (n3, e) => n4
    | (n3, f) => n4
    | (n3, g) => n4
    | (n3, h) => n4
    (* n4 + _ *)
    | (n4, n1) => n4
    | (n4, n2) => n4
    | (n4, n3) => n4
    | (n4, n4) => n4
    | (n4, a) => n4
    | (n4, b) => n4
    | (n4, c) => n4
    | (n4, d) => n4
    | (n4, e) => n4
    | (n4, f) => n4
    | (n4, g) => n4
    | (n4, h) => n4
    (* a + _ *)
    | (a, n1) => n2
    | (a, n2) => n3
    | (a, n3) => n4
    | (a, n4) => n4
    | (a, a) => b
    | (a, b) => n4
    | (a, c) => b
    | (a, d) => n3
    | (a, e) => h
    | (a, f) => n3
    | (a, g) => n3
    | (a, h) => n4
    (* b + _ *)
    | (b, n1) => n3
    | (b, n2) => n4
    | (b, n3) => n4
    | (b, n4) => n4
    | (b, a) => n4
    | (b, b) => n4
    | (b, c) => n4
    | (b, d) => n4
    | (b, e) => n4
    | (b, f) => n4
    | (b, g) => n4
    | (b, h) => n4
    (* c + _ *)
    | (c, n1) => d
    | (c, n2) => n3
    | (c, n3) => n4
    | (c, n4) => n4
    | (c, a) => b
    | (c, b) => n4
    | (c, c) => b
    | (c, d) => n3
    | (c, e) => n3
    | (c, f) => n3
    | (c, g) => n3
    | (c, h) => n4
    (* d + _ *)
    | (d, n1) => n3
    | (d, n2) => n4
    | (d, n3) => n4
    | (d, n4) => n4
    | (d, a) => n3
    | (d, b) => n4
    | (d, c) => n3
    | (d, d) => n4
    | (d, e) => n4
    | (d, f) => n4
    | (d, g) => n4
    | (d, h) => n4
    (* e + _ *)
    | (e, n1) => n3
    | (e, n2) => n4
    | (e, n3) => n4
    | (e, n4) => n4
    | (e, a) => h
    | (e, b) => n4
    | (e, c) => n3
    | (e, d) => n4
    | (e, e) => n4
    | (e, f) => n3
    | (e, g) => h
    | (e, h) => n4
    (* f + _ *)
    | (f, n1) => n3
    | (f, n2) => n4
    | (f, n3) => n4
    | (f, n4) => n4
    | (f, a) => n3
    | (f, b) => n4
    | (f, c) => n3
    | (f, d) => n4
    | (f, e) => n3
    | (f, f) => n4
    | (f, g) => n3
    | (f, h) => n4
    (* g + _ *)
    | (g, n1) => n3
    | (g, n2) => n4
    | (g, n3) => n4
    | (g, n4) => n4
    | (g, a) => n3
    | (g, b) => n4
    | (g, c) => n3
    | (g, d) => n4
    | (g, e) => h
    | (g, f) => n3
    | (g, g) => n4
    | (g, h) => n4
    (* h + _ *)
    | (h, n1) => n4
    | (h, n2) => n4
    | (h, n3) => n4
    | (h, n4) => n4
    | (h, a) => n4
    | (h, b) => n4
    | (h, c) => n4
    | (h, d) => n4
    | (h, e) => n4
    | (h, f) => n4
    | (h, g) => n4
    | (h, h) => n4
  end.

Definition bymult b1 b2 :=
  match (b1, b2) with
    | (n1, n1) => n1
    | (n1, n2) => n2
    | (n1, n3) => n3
    | (n1, n4) => n4
    | (n1, a) => a
    | (n1, b) => b
    | (n1, c) => c
    | (n1, d) => d
    | (n1, e) => e
    | (n1, f) => f
    | (n1, g) => g
    | (n1, h) => h
    (* n2 * _ *)
    | (n2, n1) => n2
    | (n2, n2) => n4
    | (n2, n3) => n4
    | (n2, n4) => n4
    | (n2, a) => b
    | (n2, b) => n4
    | (n2, c) => b
    | (n2, d) => n4
    | (n2, e) => n4
    | (n2, f) => n4
    | (n2, g) => n4
    | (n2, h) => n4
    (* n3 * _ *)
    | (n3, n1) => n3
    | (n3, n2) => n4
    | (n3, n3) => n4
    | (n3, n4) => n4
    | (n3, a) => n4
    | (n3, b) => n4
    | (n3, c) => n4
    | (n3, d) => n4
    | (n3, e) => n4
    | (n3, f) => n4
    | (n3, g) => n4
    | (n3, h) => n4
    (* n4 * _ *)
    | (n4, n1) => n4
    | (n4, n2) => n4
    | (n4, n3) => n4
    | (n4, n4) => n4
    | (n4, a) => n4
    | (n4, b) => n4
    | (n4, c) => n4
    | (n4, d) => n4
    | (n4, e) => n4
    | (n4, f) => n4
    | (n4, g) => n4
    | (n4, h) => n4
    (* a * _ *)
    | (a, n1) => a
    | (a, n2) => b
    | (a, n3) => n4
    | (a, n4) => n4
    | (a, a) => c
    | (a, b) => b
    | (a, c) => c
    | (a, d) => b
    | (a, e) => h
    | (a, f) => n4
    | (a, g) => n4
    | (a, h) => n4
    (* b * _ *)
    | (b, n1) => b
    | (b, n2) => n4
    | (b, n3) => n4
    | (b, n4) => n4
    | (b, a) => b
    | (b, b) => n4
    | (b, c) => b
    | (b, d) => n4
    | (b, e) => n4
    | (b, f) => n4
    | (b, g) => n4
    | (b, h) => n4
    (* c * _ *)
    | (c, n1) => c
    | (c, n2) => b
    | (c, n3) => n4
    | (c, n4) => n4
    | (c, a) => c
    | (c, b) => b
    | (c, c) => c
    | (c, d) => b
    | (c, e) => n4
    | (c, f) => n4
    | (c, g) => n4
    | (c, h) => n4
    (* d * _ *)
    | (d, n1) => d
    | (d, n2) => n4
    | (d, n3) => n4
    | (d, n4) => n4
    | (d, a) => b
    | (d, b) => n4
    | (d, c) => b
    | (d, d) => n4
    | (d, e) => n4
    | (d, f) => n4
    | (d, g) => n4
    | (d, h) => n4
    (* e * _ *)
    | (e, n1) => e
    | (e, n2) => n4
    | (e, n3) => n4
    | (e, n4) => n4
    | (e, a) => h
    | (e, b) => n4
    | (e, c) => n4
    | (e, d) => n4
    | (e, e) => n4
    | (e, f) => n4
    | (e, g) => h
    | (e, h) => n4
    (* f * _ *)
    | (f, n1) => f
    | (f, n2) => n4
    | (f, n3) => n4
    | (f, n4) => n4
    | (f, a) => n4
    | (f, b) => n4
    | (f, c) => n4
    | (f, d) => n4
    | (f, e) => n4
    | (f, f) => n4
    | (f, g) => n4
    | (f, h) => n4
    (* g * _ *)
    | (g, n1) => g
    | (g, n2) => n4
    | (g, n3) => n4
    | (g, n4) => n4
    | (g, a) => n4
    | (g, b) => n4
    | (g, c) => n4
    | (g, d) => n4
    | (g, e) => h
    | (g, f) => n4
    | (g, g) => n4
    | (g, h) => n4
    (* h * _ *)
    | (h, n1) => h
    | (h, n2) => n4
    | (h, n3) => n4
    | (h, n4) => n4
    | (h, a) => n4
    | (h, b) => n4
    | (h, c) => n4
    | (h, d) => n4
    | (h, e) => n4
    | (h, f) => n4
    | (h, g) => n4
    | (h, h) => n4
  end.

Definition byexp b1 b2 :=
  match (b1, b2) with
    | (n1, n1) => n1
    | (n1, n2) => n1
    | (n1, n3) => n1
    | (n1, n4) => n1
    | (n1, a) => n1
    | (n1, b) => n1
    | (n1, c) => n1
    | (n1, d) => n1
    | (n1, e) => n1
    | (n1, f) => n1
    | (n1, g) => n1
    | (n1, h) => n1
    (* n2 * _ *)
    | (n2, n1) => n2
    | (n2, n2) => n4
    | (n2, n3) => n4
    | (n2, n4) => n4
    | (n2, a) => n4
    | (n2, b) => n4
    | (n2, c) => n4
    | (n2, d) => n4
    | (n2, e) => f
    | (n2, f) => n4
    | (n2, g) => n4
    | (n2, h) => n4
    (* n3 * _ *)
    | (n3, n1) => n3
    | (n3, n2) => n4
    | (n3, n3) => n4
    | (n3, n4) => n4
    | (n3, a) => e
    | (n3, b) => n4
    | (n3, c) => n4
    | (n3, d) => n4
    | (n3, e) => g
    | (n3, f) => n4
    | (n3, g) => e
    | (n3, h) => h
    (* n4 * _ *)
    | (n4, n1) => n4
    | (n4, n2) => n4
    | (n4, n3) => n4
    | (n4, n4) => n4
    | (n4, a) => n4
    | (n4, b) => n4
    | (n4, c) => n4
    | (n4, d) => n4
    | (n4, e) => n4
    | (n4, f) => n4
    | (n4, g) => n4
    | (n4, h) => n4
    (* a * _ *)
    | (a, n1) => a
    | (a, n2) => c
    | (a, n3) => c
    | (a, n4) => c
    | (a, a) => c
    | (a, b) => c
    | (a, c) => c
    | (a, d) => c
    | (a, e) => c
    | (a, f) => c
    | (a, g) => c
    | (a, h) => c
    (* b * _ *)
    | (b, n1) => b
    | (b, n2) => n4
    | (b, n3) => n4
    | (b, n4) => n4
    | (b, a) => n4
    | (b, b) => n4
    | (b, c) => n4
    | (b, d) => n4
    | (b, e) => n4
    | (b, f) => n4
    | (b, g) => n4
    | (b, h) => n4
    (* c * _ *)
    | (c, n1) => c
    | (c, n2) => c
    | (c, n3) => c
    | (c, n4) => c
    | (c, a) => c
    | (c, b) => c
    | (c, c) => c
    | (c, d) => c
    | (c, e) => c
    | (c, f) => c
    | (c, g) => c
    | (c, h) => c
    (* d * _ *)
    | (d, n1) => d
    | (d, n2) => n4
    | (d, n3) => n4
    | (d, n4) => n4
    | (d, a) => f
    | (d, b) => n4
    | (d, c) => n4
    | (d, d) => n4
    | (d, e) => n4
    | (d, f) => n4
    | (d, g) => n4
    | (d, h) => n4
    (* e * _ *)
    | (e, n1) => e
    | (e, n2) => n4
    | (e, n3) => n4
    | (e, n4) => n4
    | (e, a) => n4
    | (e, b) => n4
    | (e, c) => n4
    | (e, d) => n4
    | (e, e) => h
    | (e, f) => n4
    | (e, g) => n4
    | (e, h) => n4
    (* f * _ *)
    | (f, n1) => f
    | (f, n2) => n4
    | (f, n3) => n4
    | (f, n4) => n4
    | (f, a) => n4
    | (f, b) => n4
    | (f, c) => n4
    | (f, d) => n4
    | (f, e) => n4
    | (f, f) => n4
    | (f, g) => n4
    | (f, h) => n4
    (* g * _ *)
    | (g, n1) => g
    | (g, n2) => n4
    | (g, n3) => n4
    | (g, n4) => n4
    | (g, a) => h
    | (g, b) => n4
    | (g, c) => n4
    | (g, d) => n4
    | (g, e) => n4
    | (g, f) => n4
    | (g, g) => h
    | (g, h) => n4
    (* h * _ *)
    | (h, n1) => h
    | (h, n2) => n4
    | (h, n3) => n4
    | (h, n4) => n4
    | (h, a) => n4
    | (h, b) => n4
    | (h, c) => n4
    | (h, d) => n4
    | (h, e) => n4
    | (h, f) => n4
    | (h, g) => n4
    | (h, h) => n4
  end.
(* end hide *)
(** We now prove that these operators have the desired properties.
    These "proofs" are just computation. We do proof by cases over all
    possible values for the variables and have _Coq_ check each case
    holds. *)

Lemma byplus_comm: forall x y, byplus x y = byplus y x.
Proof.
  destruct x; destruct y; auto. 
Qed.

Lemma byplus_assoc: 
  forall x y z, byplus x (byplus y z) = byplus (byplus x y) z.
(* begin hide *)
Proof.
  destruct x; destruct y; destruct z; auto. 
Qed.
(* end hide *)

Lemma bymult_comm: forall x y, bymult x y = bymult y x.
(* begin hide *)
Proof.
  destruct x; destruct y; auto. 
Qed.
(* end hide *)

Lemma bymult_assoc: 
  forall x y z, bymult x (bymult y z) = bymult (bymult x y) z.
(* begin hide *)
Proof.
  destruct x; destruct y; destruct z; auto. 
Qed.
(* end hide *)

Lemma bymult_ident:
  forall x, bymult x n1 = x.
(* begin hide *)
Proof.
  destruct x; auto.
Qed.
(* end hide *)

Lemma bymult_distr:
  forall x y z, bymult x (byplus y z) = byplus (bymult x y) (bymult x z).
(* begin hide *)
Proof.
  destruct x; destruct y; destruct z; auto.
Qed.
(* end hide *)

Lemma byexp_one:
  forall x, byexp x n1 = x.
(* begin hide *)
Proof.
  destruct x; auto.
Qed.
(* end hide *)

Lemma byexp_base_one:
  forall x, byexp n1 x = n1.
(* begin hide *)
Proof.
  destruct x; auto.
Qed.
(* end hide *)

Lemma byexp_byplus:
  forall x y z, byexp x (byplus y z) = bymult (byexp x y) (byexp x z).
(* begin hide *)
Proof.
  destruct x; destruct y; destruct z; auto.
Qed.
(* end hide *)

Lemma byexp_bymult:
  forall x y z, byexp (bymult x y) z = bymult (byexp x z) (byexp y z).
(* begin hide *)
Proof.
  destruct x; destruct y; destruct z; auto.
Qed.
(* end hide *)

Lemma byexp_exp:
  forall x y z, byexp (byexp x y) z = byexp x (bymult y z).
(* begin hide *)
Proof.
  destruct x; destruct y; destruct z; auto.
Qed.
(* end hide *)

(** Now we can define a denotation for expressions to 
    [byalg] terms, just as we did with [denote] and [denotez] *)

Fixpoint denote_by (e: expression) (f: nat -> byalg) : byalg :=
  (match e with
    | Var n => f n
    | Const n => 
        match n with 
         | 1 => n1
         | 2 => n2
         | 3 => n3
         | _ => n4
        end    
    | Eplus e1 e2 => byplus (denote_by e1 f) (denote_by e2 f)
    | Etimes e1 e2 => bymult (denote_by e1 f) (denote_by e2 f)
    | Epow e1 e2 => byexp (denote_by e1 f) (denote_by e2 f)
  end)%positive.

(** And we can also prove that the [td] proofs are sound under this
    denotation. The properties of [byplus], [bymult], and [byexp] that
    we've shown above cover the eleven cases corresponding to the high
    school identities.

    However, recall that we also had rules showing that constants
    could be "folded", e.g. that [Const p1 + Const p2 [=] Const (p1 +
    p2)] and so on. These turn out to be the most annoying part of the
    proof. Luckily, the proof works because of the way the operators
    treat the elements [n1], [n2], [n3], and [n4]. For example:

    - [byplus n1 n2 = n3]
    - [bymult n2 n2 = n4]
    - [bymult n3 n2 = n4]

    What's happening is that in the case of [byplus n1 n2], we treat
    n1 and n2 as though they are 1 and 2 respectively, add them to get
    3 and then we return n3. The same thing happens for the other
    operators.  Now what happens if the resulting number is greater
    than 4, as in the case with [bymult n3 n2], (since 3*2 = 6)? In
    that case we just return n4.

    Once we realize this pattern, we can prove that the constant
    folding rules are sound. Addition and multiplication are handled
    just by brute force case work. However, this didn't work for
    exponentiation, so we need a few helper lemmas first. *)

Lemma denote_by_const_gt_3:
  (forall p1, p1 > 3 -> (forall f, denote_by (Const p1) f = n4))%positive.
(* begin hide *)
Proof.
  intros.
  induction p1 using Pind.
    apply nat_of_P_gt_Gt_compare_morphism in H; compute in H;
    assert False by omega; contradiction.
  induction p1 using Pind.
    apply nat_of_P_gt_Gt_compare_morphism in H; compute in H;
    assert False by omega; contradiction.
  induction p1 using Pind.
    apply nat_of_P_gt_Gt_compare_morphism in H; compute in H;
    assert False by omega; contradiction.
  simpl.
  repeat rewrite Pplus_one_succ_l.
  assert (1 + (1 + (1 + p1)) = 3 + p1)%positive.
  apply nat_of_P_inj.
  repeat rewrite nat_of_P_plus_morphism. simpl. auto. 
  rewrite H0.
  simpl.
  destruct p1; try destruct p1; auto.
Qed.
(* end hide *)

Lemma Ppow_increase: (forall p2 p1, p1 ^ p2 > p1 \/ p1 ^ p2 = p1)%positive.
(* begin hide *)
Proof.
  induction p2 using Pind; intros.
  right. apply exp_one.
  rewrite Pplus_one_succ_l.
  rewrite exp_plus. 
  rewrite exp_one.
  specialize (IHp2 p1).
  destruct IHp2.
  left.
  apply nat_of_P_gt_Gt_compare_complement_morphism. 
  apply nat_of_P_gt_Gt_compare_morphism in H.
  rewrite nat_of_P_mult_morphism. 
  specialize (ZL4 p1). intros. destruct H0.
  rewrite H0 in *. 
  assert (S x * 1 = S x)%nat by omega.
  rewrite <-H1 at 2.
  assert (S x * 1 < S x * nat_of_P (p1 ^ p2))%nat.
  auto with *.
  omega.
  rewrite H.
  assert (nat_of_P p1 = 1 \/ nat_of_P p1 > 1)%nat.
    specialize (ZL4 p1). intros. destruct H0.
    omega.
  destruct H0.
  replace 1%nat with (nat_of_P 1) in H0 by auto.
  apply nat_of_P_inj in H0.
  rewrite H0. auto with *.
  left.
  apply nat_of_P_gt_Gt_compare_complement_morphism. 
  rewrite nat_of_P_mult_morphism. 
  assert (nat_of_P p1 * 1 = nat_of_P p1)%nat by omega.
  rewrite <-H1 at 3.
  assert (1 * nat_of_P p1 < nat_of_P p1 * nat_of_P p1)%nat.
  apply mult_lt_compat_r.
  auto with *. auto with *.
  auto with *.
Qed.
(* end hide *)

Lemma Ppow_gt_3: (forall p2 p1, p1 > 1 -> p2 > 1 -> p1 ^ p2 > 3)%positive.
(* begin hide *)
Proof.
  induction p2 using Pind; intros.
    apply nat_of_P_gt_Gt_compare_morphism in H0; compute in H0;
    assert False by omega; contradiction.
  rewrite Pplus_one_succ_l.
  rewrite exp_plus.
  rewrite exp_one.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  rewrite nat_of_P_mult_morphism. 
  specialize (Ppow_increase p2 p1). intros.
  destruct H1.
  apply nat_of_P_gt_Gt_compare_morphism in H1.
  simpl.
  apply nat_of_P_gt_Gt_compare_morphism in H.
  replace (nat_of_P 1) with 1%nat in H by auto.
  assert (nat_of_P p1 >= 2)%nat. auto with *. 
  assert (2 * 2 <= nat_of_P p1 * nat_of_P (p1 ^ p2))%nat.
  apply mult_le_compat; auto with *.
  auto with *.
  rewrite H1.
  simpl.
  apply nat_of_P_gt_Gt_compare_morphism in H.
  replace (nat_of_P 1) with 1%nat in H by auto.
  assert (nat_of_P p1 >= 2)%nat. auto with *. 
  assert (2 * 2 <= nat_of_P p1 * nat_of_P p1)%nat.
  apply mult_le_compat; auto with *.
  auto with *.
Qed.
(* end hide *)

Local Open Scope positive_scope.
Local Open Scope expression_scope.

Lemma positive_range: forall p: positive, p > 1 \/ p = 1.
(* begin hide *)
Proof.
  intros. specialize (ZL11 p); intros.
  destruct H. right; auto.
  left. specialize (ZL4 p). intros.
  destruct H0.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  rewrite H0. compute.
  assert (x <> O). unfold not; intros.
  rewrite H1 in H0. 
  replace 1%nat with (nat_of_P 1) in H0 by auto.
  apply nat_of_P_inj in H0.
  contradiction.
  omega.
Qed.
(* end hide *)

Lemma constants_pow_gt_1: forall p1 p2 f, p1 > 1 -> p2 > 1 ->
  denote_by (Const p1 ^ Const p2) f =
      denote_by (Const (p1 ^ p2)) f.
(* begin hide *)
Proof.
  intros.
  rewrite denote_by_const_gt_3. 
  simpl. 
  induction p1 using Pind. 
    apply nat_of_P_gt_Gt_compare_morphism in H; compute in H;
    assert False by omega; contradiction.
  destruct (Psucc p1); try destruct p.
  induction p2 using Pind; auto;
  destruct (Psucc p2); try destruct p0; auto.
  induction p2 using Pind; auto;
  destruct (Psucc p2); try destruct p0; auto.
  induction p2 using Pind; auto.
    apply nat_of_P_gt_Gt_compare_morphism in H0; compute in H0;
    assert False by omega; contradiction.
  destruct (Psucc p2); try destruct p; auto.
  induction p2 using Pind; auto.
    apply nat_of_P_gt_Gt_compare_morphism in H0; compute in H0;
    assert False by omega; contradiction.
  destruct p2. destruct p2. auto.
   auto. auto. destruct p2. auto. auto. auto.
   auto. destruct p2. destruct p2. auto.
   auto. auto. destruct p2. auto.
   auto. auto. auto. 
  destruct p2. destruct p2.
   auto.
   auto.
   auto.
  destruct p2.
   auto.
   auto.
   auto.
    apply nat_of_P_gt_Gt_compare_morphism in H0; compute in H0;
    assert False by omega; contradiction.
    apply nat_of_P_gt_Gt_compare_morphism in H; compute in H;
    assert False by omega; contradiction.
  apply Ppow_gt_3; auto.
Qed.
(* end hide *)

Lemma constant_pow: 
  forall p2 p1 f, denote_by (Const p1 ^ Const p2) f =
      denote_by (Const (p1 ^ p2)) f.
(* begin hide *)
Proof.
  intros.
  specialize (positive_range p1). 
  specialize (positive_range p2); intros.
  destruct H.
  destruct H0.
  apply constants_pow_gt_1; auto.
  rewrite H0. simpl.
  rewrite byexp_base_one.  
  rewrite unit_power.
  auto.
  rewrite H.
  simpl. 
  rewrite byexp_one.
  rewrite exp_one.
  auto.
Qed.
(* end hide *)

(** With those out of the way, we proceed with the soundness 
    proof. *)

Lemma td_sound_by: 
 forall x y, x [=] y -> forall f, denote_by x f = denote_by y f.
Proof.
  intros.
  induction H; try (apply constant_pow); simpl.
  simpl; rewrite IHtd1; rewrite IHtd2; auto with *.
  simpl; rewrite IHtd1; rewrite IHtd2; auto with *.
  simpl; rewrite IHtd1; rewrite IHtd2; auto with *.

  intros; simpl; repeat (induction p1; induction p2; auto with *);
  repeat (induction p1; auto with *);
  repeat (induction p2; auto with *).
  intros; simpl; repeat (induction p1; induction p2; auto with *);
  repeat (induction p1; auto with *);
  repeat (induction p2; auto with *).
  auto.  
  rewrite IHtd1; rewrite IHtd2; auto.
  auto.

  apply byplus_comm.
  rewrite byplus_assoc; auto.
  apply bymult_ident.
  apply bymult_comm.
  rewrite bymult_assoc; auto.
  apply bymult_distr.
  apply byexp_base_one.
  apply byexp_one.
  apply byexp_byplus.
  apply byexp_bymult.
  apply byexp_exp.
Qed.

(** Next we show that under the Burris and Yeats algebra denotation,
   [w1] is not equal to [w2]. Specifically, when [x = a] and [y = e], the
   two expressions are not equal. *)

Lemma w1_neq_w2_by: ~ (forall f, denote_by w1 f = denote_by w2 f).
Proof. 
  intros. unfold not.
  intros.  
  specialize (H (fun x => match x with | O => a | _ => e end)).
  compute in H.
  inversion H.
Qed.

(** Which implies that we cannot have [w1 [=] w2], as discussed
    earlier. *)

Theorem not_td_w1_w2: ~ (w1 [=] w2).
Proof.
 unfold not; intro.
 eapply w1_neq_w2_by.
 apply td_sound_by; auto.
Qed.

(** One might ask what needs to be added to the set of eleven
    identities to make them complete.  Unfortunately, R. Gurevic showed
    that a finite list of identities cannot be complete. However, that
    proof is considerably harder, so this seems like a good place to
    wrap up!

    #<i>Thanks to Edward Gan for his feedback.</i>#
    
    #<b>References:</b>#
   
    R. Gurevic. Equational theory of positive numbers with
    exponentiation is not finitely axiomatizable. _Ann. Pure
    Appl. Logic_, 49(1):1-30, 1990.

    Stanley N. Burris and Karen A. Yeats. The saga of the high school
    identities. _Algebra Universalis_, 52(2-3):325-342, 2004.

    A. J. Wilkie. On exponentiation - a solution to Tarski's high
    school algebra problem. *)

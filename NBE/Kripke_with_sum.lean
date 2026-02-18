namespace KripkeWithSum


abbrev Var := Nat

inductive Formula: Type where
  | atom: Var -> Formula
  | imp: Formula -> Formula -> Formula
  | or: Formula -> Formula -> Formula


abbrev Context := List Formula


inductive Context.proves: Context -> Formula -> Prop where
  | var {Γ: Context} {A: Formula}: A ∈ Γ -> Γ.proves A
  | abs {Γ: Context} {A B: Formula}: Context.proves (A :: Γ: Context) B -> Γ.proves (A.imp B)
  | app {Γ: Context} {A B: Formula}: Γ.proves (A.imp B) -> Γ.proves A -> Γ.proves B
  | inl {Γ: Context} {A B: Formula}: Γ.proves A -> Γ.proves (A.or B)
  | inr {Γ: Context} {A B: Formula}: Γ.proves B -> Γ.proves (A.or B)
  | case {Γ: Context} {A B C: Formula}:
    Γ.proves (A.or B) ->
    Context.proves (A :: Γ) C ->
    Context.proves (B :: Γ) C ->
    Γ.proves C


@[simp]
theorem Context.proves_cons (Γ: Context) (A: Formula):
  Context.proves (A :: Γ) A
:= by
  apply Context.proves.var
  simp


-- the only thing needed
theorem Context.proves.weaken {Γ Γ': Context} {A: Formula}:
  Γ.proves A ->
  Γ.Sublist Γ' ->
  Γ'.proves A
:= by
  intro H R
  induction H generalizing Γ' with
  | var | abs | app =>
    grind [var, abs, app]
  | inl | inr | case =>
    grind [inl, inr, case]


def Context.forces (Γ: Context) (A: Formula) : Prop := match A with
  | .atom n => Γ.proves (.atom n)
  | .imp P Q => forall Γ': Context, Γ.Sublist Γ' -> Context.forces Γ' P -> Context.forces Γ' Q
  | .or P Q => Γ.forces P ∨ Γ.forces Q


def Context.forces.weaken {Γ Γ': Context} {A: Formula}:
  Γ.forces A ->
  Γ.Sublist Γ' ->
  Γ'.forces A
:= by
  intro F R
  induction A generalizing Γ'
  case atom n =>
    simp [Context.forces] at *
    apply Context.proves.weaken F R
  case imp P Q IHP IHQ =>
    simp [Context.forces] at *
    intro Γ'' R' F'
    apply F
    . apply List.Sublist.trans
      . exact R
      . exact R'
    . exact F'
  case or P Q IHP IHQ =>
    simp [Context.forces] at *
    cases F with
    | inl F =>
      left
      apply IHP F R
    | inr F =>
      right
      apply IHQ F R


def Context.entails (Γ: Context) (A: Formula): Prop :=
  forall Δ: Context, (forall B: Formula, B ∈ Γ -> Δ.forces B) -> Δ.forces A


theorem soundness {Γ: Context} {A: Formula}:
  Γ.proves A -> Γ.entails A
:= by
  intro HT
  intro Δ HPre
  induction HT generalizing Δ
  case var Γ A H =>
    apply HPre
    exact H
  case abs Γ A B H IH =>
    simp [Context.forces]
    intro Γ' R F
    apply IH
    simp
    and_intros
    . exact F
    . intro T H
      apply Context.forces.weaken _ R
      apply HPre
      exact H
  case app Γ A B H1 H2 IH1 IH2 =>
    specialize IH1 Δ HPre
    specialize IH2 Δ HPre
    simp [Context.forces] at IH1
    apply IH1
    . simp
    . exact IH2
  case inl Γ A B H IH =>
    simp [Context.forces]
    left
    apply IH
    exact HPre
  case inr Γ A B H IH =>
    simp [Context.forces]
    right
    apply IH
    exact HPre
  case case Γ A B C H H1 H2 IH IH1 IH2 =>
    simp [Context.forces] at *
    specialize IH _ HPre
    cases IH with
    | inl F =>
      apply IH1
      . exact F
      . exact HPre
    | inr F =>
      apply IH2
      . exact F
      . exact HPre



/--
This should corresponds to a _basis_ of a Grothendieck topology.
-/
def Cover (L: List Context) (Γ: Context): Prop :=
  (forall Δ: Context, Δ ∈ L -> Γ.Sublist Δ)
  ∧
  (forall A: Formula, (forall Δ: Context, Δ ∈ L -> Δ.proves A) -> Γ.proves A)


theorem Cover.sub {L: List Context} {Γ: Context}:
  Cover L Γ ->
  forall Δ: Context, Δ ∈ L -> Γ.Sublist Δ
:= by
  intro ⟨S, P⟩
  exact S


theorem Cover.proves {L: List Context} {Γ: Context}:
  Cover L Γ ->
  forall A: Formula, (forall Δ: Context, Δ ∈ L -> Δ.proves A) -> Γ.proves A
:= by
  intro ⟨S, P⟩
  exact P


@[simp]
theorem Cover.self {Γ: Context}:
  Cover [Γ] Γ
:= by
  and_intros
  . simp
  . intro Δ H
    simp at H
    exact H


theorem Cover.or {Γ: Context} {P Q: Formula}:
  Γ.proves (P.or Q) ->
  Cover [P :: Γ, Q :: Γ] Γ
:= by
  intro H
  and_intros
  . simp
  . intro A K
    simp at K
    obtain ⟨HP, HQ⟩ := K
    apply H.case
    . exact HP
    . exact HQ


def Context.forces' (Γ: Context) (A: Formula) : Prop := match A with
  | .atom n => Γ.proves (.atom n)
  | .imp P Q => forall Γ': Context, Γ.Sublist Γ' -> Context.forces' Γ' P -> Context.forces' Γ' Q
  | .or P Q => exists L: List Context, Cover L Γ ∧ (forall Δ: Context, Δ ∈ L -> Context.forces' Δ P ∨ Context.forces' Δ Q)


theorem sheaf_iff' {Γ: Context} {A: Formula}:
  Γ.proves A <-> Γ.forces' A
:= by
  induction A generalizing Γ
  case atom n =>
    simp [Context.forces']
  case imp P Q IHP IHQ =>
    apply Iff.intro
    . intro H
      simp [Context.forces']
      intro Γ' R F
      apply IHQ.mp
      apply Context.proves.app
      . apply H.weaken
        exact R
      . apply IHP.mpr
        exact F
    . intro F
      simp [Context.forces'] at F
      apply Context.proves.abs
      apply IHQ.mpr
      apply F
      . simp
      . apply IHP.mp
        simp
  case or P Q IHP IHQ =>
    apply Iff.intro
    . intro H
      simp [Context.forces']
      let L := [P::Γ, Q::Γ]
      have IHP := IHP.mp (Context.proves_cons Γ P)
      have IHQ := IHQ.mp (Context.proves_cons Γ Q)
      exists L
      apply And.intro
      . unfold L
        apply Cover.or
        exact H
      . intro Δ I
        unfold L at I
        simp at I
        rcases I with I | I
        . left
          simp_all
        . right
          simp_all
    . intro F
      simp [Context.forces'] at F
      obtain ⟨L, C, F⟩ := F
      apply C.proves
      intro Δ I
      specialize F Δ I
      rcases F with F | F
      . apply Context.proves.inl
        apply IHP.mpr
        exact F
      . apply Context.proves.inr
        apply IHQ.mpr
        exact F


theorem Context.forces'.weaken {Γ Γ': Context} {A: Formula}:
  Γ.forces' A ->
  Γ.Sublist Γ' ->
  Γ'.forces' A
:= by
  intro F R
  apply sheaf_iff'.mp
  apply Context.proves.weaken
  . apply sheaf_iff'.mpr
    exact F
  . exact R


def Context.entails' (Γ: Context) (A: Formula): Prop :=
  forall Δ: Context, (forall B: Formula, B ∈ Γ -> Δ.forces' B) -> Δ.forces' A


theorem soundness' {Γ: Context} {A: Formula}:
  Γ.proves A -> Γ.entails' A
:= by
  intro HT
  intro Δ HPre
  induction HT generalizing Δ
  case var Γ A H =>
    apply HPre
    exact H
  case abs Γ A B H IH =>
    simp [Context.forces']
    intro Γ' R F
    apply IH
    simp
    and_intros
    . exact F
    . intro T H
      apply Context.forces'.weaken _ R
      apply HPre
      exact H
  case app Γ A B H1 H2 IH1 IH2 =>
    specialize IH1 Δ HPre
    specialize IH2 Δ HPre
    simp [Context.forces'] at IH1
    apply IH1
    . simp
    . exact IH2
  case inl Γ A B H IH =>
    simp [Context.forces']
    exists [Δ]
    apply And.intro
    . apply Cover.self
    . simp
      left
      apply IH
      exact HPre
  case inr Γ A B H IH =>
    simp [Context.forces']
    exists [Δ]
    apply And.intro
    . apply Cover.self
    . simp
      right
      apply IH
      exact HPre
  case case Γ T1 T2 T H H1 H2 IH IH1 IH2 =>
    simp [Context.forces'] at *
    specialize IH Δ HPre
    obtain ⟨L, C, F⟩ := IH
    apply sheaf_iff'.mp
    apply C.proves
    intro Δ' I'
    apply sheaf_iff'.mpr
    specialize F Δ' I'
    cases F with
    | inl F =>
      apply IH1
      . exact F
      . intro τ I
        specialize HPre τ I
        apply HPre.weaken
        apply C.sub Δ' I'
    | inr F =>
      apply IH2
      . exact F
      . intro τ I
        specialize HPre τ I
        apply HPre.weaken
        apply C.sub Δ' I'


theorem completeness' {Γ: Context} {A: Formula}:
  Γ.entails' A -> Γ.proves A
:= by
  intro H
  specialize H Γ
  apply sheaf_iff'.mpr
  apply H
  intro B I
  apply sheaf_iff'.mp
  apply Context.proves.var I

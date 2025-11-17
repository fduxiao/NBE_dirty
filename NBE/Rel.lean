abbrev Relation (X: Type) := X -> X -> Prop

class Congruence {X: Type} (R: Relation X) (f: X -> X) where
  cong: forall {x y: X}, R x y -> R (f x) (f y)

class KeepCong {X: Type} (R S: Relation X) where
  keep_cong: forall (f: X -> X),
    (forall {x y}, (R x y) -> R (f x) (f y)) ->
    forall {x y}, (S x y) -> S (f x) (f y)


def Relation.keep_cong {X: Type}
  {R S: Relation X} (f: X -> X)
  [inst: KeepCong R S]:
    (forall {x y}, (R x y) -> R (f x) (f y)) ->
    forall {x y}, (S x y) -> S (f x) (f y) :=
    inst.keep_cong f


inductive RTCl {X} (R: Relation X): Relation X where
  | refl {x: X}: RTCl R x x
  | step {x y z: X}: R x y -> RTCl R y z -> RTCl R x z


theorem RTCl.inclusion {X} {R: Relation X} {x y}:
  R x y -> RTCl R x y
:= by
  intro H
  apply RTCl.step
  . exact H
  . apply RTCl.refl


@[refl]
theorem RTCl.is_refl {X} {R: Relation X} {x}:
  RTCl R x x
:= by
  constructor


theorem RTCl.trans {X} {R: Relation X} {x y z}:
  RTCl R x y -> RTCl R y z -> RTCl R x z
:= by
  intro Hxy Hyz
  induction Hxy
  case refl =>
    trivial
  case step =>
    apply RTCl.step <;> solve_by_elim


instance {X} {R: Relation X}: Trans (RTCl R) (RTCl R) (RTCl R) where
  trans := RTCl.trans


instance {X} {R: Relation X}: KeepCong R (RTCl R) where
  keep_cong := by
    intro f HCong x y HR
    induction HR with
    | refl =>
      apply RTCl.refl
    | @step x y z Hxy Hyz IHyz =>
      have Hfxy := (HCong Hxy)
      apply RTCl.step Hfxy IHyz


theorem RTCl.keep_cong {X} {R: Relation X} {f: X -> X}:
  (forall {x y}, (R x y) -> R (f x) (f y)) ->
    forall {x y}, (RTCl R x y) -> RTCl R (f x) (f y)
:= by
  apply R.keep_cong (S := RTCl R)


inductive ECl {X} (R: Relation X): Relation X where
  | refl {x}: ECl R x x
  | step {x y z}: R x y -> ECl R y z -> ECl R x z
  | rstep {x y z}: R y x -> ECl R y z -> ECl R x z


theorem ECl.inclusion {X} {R: Relation X} {x y: X}:
  R x y -> ECl R x y
:= by
  intro H
  apply step
  . exact H
  . apply refl


theorem ECl.reverse {X} {R: Relation X} {x y: X}:
  R x y -> ECl R y x
:= by
  intro H
  apply rstep
  . exact H
  . apply refl


theorem ECl.trans {X} {R: Relation X} {x y z: X}:
  ECl R x y -> ECl R y z -> ECl R x z
:= by
  intro S H
  induction S with
  | refl =>
    exact H
  | rstep =>
    apply rstep <;> solve_by_elim
  | step =>
    apply step <;> solve_by_elim


@[refl]
theorem ECl.is_refl {X} {R: Relation X} {x}:
  ECl R x x
:= by
  apply refl


@[symm]
theorem ECl.symm {X} {R: Relation X} {x y}:
  ECl R x y -> ECl R y x
:= by
  intro S
  induction S with
  | rstep S H IH =>
    apply trans
    . exact IH
    . apply inclusion
      exact S
  | refl =>
    apply refl
  | step Hxy Hyz IHyz =>
    apply trans
    . exact IHyz
    . apply rstep
      . exact Hxy
      . apply refl


instance {X} {R: Relation X}: Trans (ECl R) (ECl R) (ECl R) where
  trans := ECl.trans



theorem RTCl.sub_ecl {X} {R: Relation X} {x y}:
  RTCl R x y -> ECl R x y
:= by
  intro H
  induction H with
  | refl =>
    rfl
  | step Hxt Hty IH =>
    rename_i x t y
    calc
      ECl R x t := by
        apply ECl.inclusion
        exact Hxt
      ECl R t y := by
        exact IH


theorem ECl.keep_cong {X} {R: Relation X} {f : X → X}:
  (∀ {x y : X}, R x y → R (f x) (f y)) → ∀ {x y : X}, ECl R x y → ECl R (f x) (f y)
:= by
  intro HCong x y HR
  induction HR with
  | refl =>
    apply ECl.refl
  | step Hxy Hyz IHyz =>
    apply ECl.step (HCong Hxy) IHyz
  | rstep Hyx Hyz IHyz =>
    apply ECl.rstep (HCong Hyx) IHyz


def Relation.Normal {X: Type} (R: Relation X) (x: X) := Not (exists y, R x y)
def Relation.MNormal {X: Type} (R: Relation X) (x: X) := forall {y}, RTCl R x y -> x = y


def Relation.Normal.MNormal {X: Type} {R: Relation X}:
  forall {x: X}, R.Normal x -> R.MNormal x
:= by
  intro n HR m HMR
  induction HMR with
  | @refl x =>
    eq_refl
  | @step a b c Hab Hbc Hbc =>
    exfalso
    apply HR
    constructor
    apply Hab


class Confluent {X: Type} (R: Relation X) where
  confl: forall {m1 m2 m3},
    RTCl R m1 m2 -> RTCl R m1 m3 -> exists m4, RTCl R m2 m4 /\ RTCl R m3 m4

def Relation.confl {X: Type} (R: Relation X) [inst: Confluent R]
  {m1 m2 m3} := inst.confl (m1 := m1) (m2 := m2) (m3 := m3)


class SemiConfluent {X: Type} (R: Relation X) where
  semi_confl: forall {m1 m2 m3}, R m1 m2 -> RTCl R m1 m3 -> exists m4, RTCl R m2 m4 /\ RTCl R m3 m4

def Relation.semi_confl {X: Type} (R: Relation X) [inst: SemiConfluent R]
  {m1 m2 m3} := inst.semi_confl (m1 := m1) (m2 := m2) (m3 := m3)


instance SemiConfluent.confluent {X: Type} (R: Relation X)
  [inst: SemiConfluent R]: Confluent R where
  confl := by
    intro m1 m2 m3
    intro H12
    revert m3
    induction H12 with
    | @refl x =>
      intro m3 H13
      exists m3
    | @step m1 b m2 H1b Hb2 IH =>
      intro m3 H13
      let ⟨x, ⟨Hbx, H3x⟩⟩ := inst.semi_confl H1b H13
      let ⟨m4, ⟨H24, Hx4⟩⟩ := IH Hbx
      exists m4
      apply And.intro
      . apply H24
      . calc
          RTCl R m3 x := by
            assumption
          RTCl R x m4 := by
            assumption


class ChurchRosser {X: Type} (R: Relation X) where
  church_rosser: forall {m2 m3},
    ECl R m2 m3 -> exists m4, RTCl R m2 m4 /\ RTCl R m3 m4


def Relation.church_rosser {X: Type} (R: Relation X) [inst: ChurchRosser R]
  {m2 m3} := inst.church_rosser (m2 := m2) (m3 := m3)


instance Confluent.church_rosser {X: Type} (R: Relation X)
  [inst: Confluent R]: ChurchRosser R where
  church_rosser := by
    intro m2 m3 H
    induction H with
    | @refl x =>
      exists x
    | @step a b c Hab Hbc IHbc =>
      let ⟨m4, ⟨Hbm4, Hcm4⟩⟩ := IHbc
      exists m4
      and_intros
      . apply RTCl.step Hab Hbm4
      . exact Hcm4
    | @rstep a b c Hba Hbc IHbc =>
      let ⟨y, Hby, Hcy⟩ := IHbc
      let ⟨m4, Hym4, Ham4⟩ := inst.confl Hby (RTCl.inclusion Hba)
      exists m4
      and_intros
      . exact Ham4
      . apply RTCl.trans
        . exact Hcy
        . exact Hym4


class Relation.NormalFormUnique {X} (R: Relation X) where
  normal_formal_unique: forall {n m1 m2},
    RTCl R n m1 -> RTCl R n m2 ->
    R.Normal m1 -> R.Normal m2 ->
    m1 = m2


instance Relation.ChRo_normal_form_unique
  {X: Type}
  {R: Relation X}
  [inst: Confluent R]
: R.NormalFormUnique where
  normal_formal_unique := by
    intro n m1 m2
    intro r1 r2 N1 N2
    have ⟨m4, ⟨H14, H24⟩⟩ := inst.confl r1 r2
    have E1 := N1.MNormal H14
    have E2 := N2.MNormal H24
    subst_eqs
    eq_refl


theorem Relation.ChRo_to_semi_confl {X: Type} (R: Relation X)
  [inst: ChurchRosser R]: SemiConfluent R where
  semi_confl := by
    intro m1 m2 m3 H12 H13
    apply inst.church_rosser
    apply ECl.trans (y := m1)
    . symm
      apply ECl.inclusion H12
    . apply RTCl.sub_ecl
      exact H13


inductive Relation.union {X: Type} (R1 R2: Relation X): Relation X where
  | left {x y}: R1 x y -> union R1 R2 x y
  | right {x y}: R2 x y -> union R1 R2 x y


theorem RTCl.left {X: Type} {R1 R2: Relation X} {x y}:
  RTCl R1 x y -> RTCl (R1.union R2) x y
:= by
  intro H
  induction H with
  | refl =>
    rfl
  | step Hxy Hyz IH =>
    rename_i x y z
    apply RTCl.step
    . apply Relation.union.left
      exact Hxy
    . exact IH


theorem RTCl.right {X: Type} {R1 R2: Relation X} {x y}:
  RTCl R2 x y -> RTCl (R1.union R2) x y
:= by
  intro H
  induction H with
  | refl =>
    rfl
  | step Hxy Hyz IH =>
    rename_i x y z
    apply RTCl.step
    . apply Relation.union.right
      exact Hxy
    . exact IH


theorem RTCl.union_rtcl {X: Type} {R1 R2: Relation X}:
  RTCl ((RTCl R1).union (RTCl R2)) = RTCl (R1.union R2)
:= by
  funext x z
  apply propext
  apply Iff.intro
  . intro H
    induction H with
    | refl =>
      rfl
    | step Hxy Hyz IH =>
      rename_i x y z
      cases Hxy with
      | left Hxy =>
        apply RTCl.trans
        . apply Hxy.left
        . exact IH
      | right Hxy =>
        apply RTCl.trans
        . apply Hxy.right
        . exact IH
  . intro H
    induction H with
    | refl =>
      rfl
    | step Hxy Hyz IH =>
      rename_i x y z
      cases Hxy with
      | left Hxy =>
        apply RTCl.step
        . apply Relation.union.left
          apply RTCl.inclusion
          apply Hxy
        . exact IH
      | right Hxy =>
        apply RTCl.step
        . apply Relation.union.right
          apply RTCl.inclusion
          apply Hxy
        . exact IH


class Commutative {X: Type} (R1 R2: Relation X) where
  /--
  ```
  x →₁ y1         x →₁ y1
  ↓₂         =>   ↓₂   ↓₂
  y2              y2 →₁ z
  ```
  -/
  comm {x y1 y2: X}: R1 x y1 -> R2 x y2 -> exists z, R2 y1 z ∧ R1 y2 z


/--
```
x →₁ y1         x →₁ y1
↡₂         =>   ↡₂   ↡₂
y2              y2 →₁ z
```
-/
theorem RTCl.semi_comm {X: Type} {R1 R2: Relation X} [inst: Commutative R1 R2]:
  forall {x y1 y2}, R1 x y1 -> RTCl R2 x y2 -> exists z, RTCl R2 y1 z ∧ R1 y2 z
:= by
  intro x y1 y2 Hxy1 Hxy2
  induction Hxy2 generalizing y1 with
  | refl =>
    /-
    x →₁ y1
    ↡₂
    x
    -/
    exists y1
  | step Hxt Hty2 IH =>
    /-
    x →₁ y1
    ↓₂   ↓₂
    t →₁ w
    ↡₂
    y2
    -/
    obtain ⟨w, Hy1w, Htw⟩ := inst.comm Hxy1 Hxt
    /-
    x  →₁ y1
    ↓₂    ↓₂
    t  →₁ w
    ↡₂    ↡₂
    y2 →₁ z
    -/
    obtain ⟨z, Hwz, Hy2z⟩ := IH Htw
    exists z
    and_intros
    . apply RTCl.step Hy1w Hwz
    . apply Hy2z


/--
```
x ↠₁ y1         x ↠₁ y1
↡₂         =>   ↡₂   ↡₂
y2              y2 ↠₁ z
```
-/
instance Commutative.rtcl {X: Type} {R1 R2: Relation X} [inst: Commutative R1 R2]:
  Commutative (RTCl R1) (RTCl R2)
where
  comm {x y1 y2} := by
    intro Hxy1 Hxy2
    induction Hxy1 generalizing y2 with
    | refl =>
      /-
      x ↠₁ x
      ↡₂
      y2
      -/
      exists y2
    | step Hxt Hty1 IH =>
      /-
      x  →₁ t ↠₁ y1
      ↡₂    ↡₂
      y2 →₁ d
      -/
      obtain ⟨d, Htd, Hy2d⟩ := RTCl.semi_comm Hxt Hxy2
      /-
      x  →₁ t ↠₁ y1
      ↡₂    ↡₂   ↡₂
      y2 →₁ d ↠₁ z
      -/
      obtain ⟨z, Hy1z, Hdz⟩ := IH Htd
      exists z
      and_intros
      . apply Hy1z
      . apply RTCl.step Hy2d Hdz


class Diamond {X: Type} (R: Relation X) where
  diamond {m1 m2 m3: X}: R m1 m2 -> R m1 m3 -> exists m4, R m2 m4 ∧ R m3 m4


instance Diamond.semi_confl {X} {R: Relation X} [inst: Diamond R]: SemiConfluent R where
  semi_confl := by
    intro m1 m2 m3 H12 H13
    induction H13 generalizing m2 with
    | refl =>
      /-
      m1 → m2
      ↓
      m1
      -/
      rename_i m1
      exists m2
      and_intros
      . rfl
      . apply RTCl.inclusion
        exact H12
    | step H1y Hy3 IH =>
      rename_i m1 y m3
      /-
      m1 → m2
      ↓    ↓
      y →  d
      ↡
      m3
      -/
      obtain ⟨d, H2d, Hyd⟩ := inst.diamond H12 H1y
      obtain ⟨m4, Hd4, H34⟩ := IH Hyd
      exists m4
      and_intros
      . apply RTCl.step H2d Hd4
      . exact H34


instance Diamond.confluence {X} {R: Relation X} [inst: Diamond R]: Confluent R where
  confl := Confluent.confl


instance Commutative.union_diamond {X} {R1 R2: Relation X}
  [comm: Commutative R1 R2] [dia1: Diamond R1] [dia2: Diamond R2]
:
  Diamond (R1.union R2)
where
  diamond {m1 m2 m3} := by
    intro H12 H13
    match H12, H13 with
    | .left H12, .left H13 =>
      obtain ⟨m4, H24, H34⟩ := dia1.diamond H12 H13
      exists m4
      and_intros
      . apply Relation.union.left H24
      . apply Relation.union.left H34
    | .left H12, .right H13 =>
      obtain ⟨m4, H24, H34⟩ := comm.comm H12 H13
      exists m4
      and_intros
      . apply Relation.union.right H24
      . apply Relation.union.left H34
    | .right H12, .left H13 =>
      obtain ⟨m4, H34, H24⟩ := comm.comm H13 H12
      exists m4
      and_intros
      . apply Relation.union.left H24
      . apply Relation.union.right H34
    | .right H12, .right H13 =>
      obtain ⟨m4, H24, H34⟩ := dia2.diamond H12 H13
      exists m4
      and_intros
      . apply Relation.union.right H24
      . apply Relation.union.right H34


instance Confluent.rtcl_diamond {X} {R: Relation X} [inst: Confluent R]: Diamond (RTCl R) where
  diamond := inst.confl


instance Relation.union_comm_confl {X} {R1 R2: Relation X}
  [comm: Commutative R1 R2] [confl1: Confluent R1] [confl2: Confluent R2]
:
  Confluent (R1.union R2)
where
  confl := by
    intro m1 m2 m3 H12 H13
    have dia1 := confl1.rtcl_diamond
    have dia2 := confl2.rtcl_diamond
    replace comm := comm.rtcl
    have dia := comm.union_diamond
    have confluence := dia.confluence
    rewrite [<-RTCl.union_rtcl] at *
    apply confluence.confl
    . assumption
    . assumption

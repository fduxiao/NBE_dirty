import NBE.SingleSortImp.BetaEta

namespace SingleSortImp.CounterExample

def Stronger (Γ' Γ: Context): Prop := exists Δ, Γ' = Δ ++ Γ

def Stronger.refl {Γ: Context}: Stronger Γ Γ
:= by
  exists []

def Stronger.comp {Γ'' Γ' Γ: Context}:
  Stronger Γ' Γ -> Stronger Γ'' Γ' -> Stronger Γ'' Γ
:= by
  rintro ⟨Δ, E⟩ ⟨Δ', E'⟩
  exists (Δ' ++ Δ)
  simp [E', E]

notation Γ' " >> " Γ => Stronger Γ' Γ


def Stronger.length {Γ' Γ: Context} (_: Γ' >> Γ): Nat := Γ'.length - Γ.length
def Stronger.diff {Γ' Γ: Context} (r: Γ' >> Γ): Context := Γ'.take (Stronger.length r)


@[simp]
theorem Stronger.diff_length {Γ' Γ: Context} (r: Γ' >> Γ):
  r.length = Γ'.length - Γ.length
:= by
  simp [Stronger.length]


theorem Stronger.diff_eq {Γ' Γ: Context} (r: Γ' >> Γ):
  Γ' = r.diff ++ Γ
:= by
  unfold Stronger.diff
  simp [Stronger.length]
  rcases r with ⟨Δ, E⟩
  simp [E]


structure Presheaf where
  obj: Context -> Type
  map {Γ' Γ: Context} (r: Γ' >> Γ): obj Γ -> obj Γ'
  map_id {Γ: Context}: forall {x: obj Γ}, map .refl x = x
  map_comp {Γ'' Γ' Γ: Context} {r': Γ'' >> Γ'} {r: Γ' >> Γ}:
     forall {x: obj Γ}, map r' (map r x) = map (Stronger.comp r r') x


structure NatTrans (F G: Presheaf) where
  trans {Γ: Context}: F.obj Γ -> G.obj Γ
  nat {Γ' Γ: Context} (r: Γ' >> Γ):
    forall {x: F.obj Γ}, trans (F.map r x) = G.map r (trans x)


def NF (T: Ty): Presheaf where
  obj Γ := {t: Tm // Tm.NF Γ t T}
  map {Γ' Γ: Context} r := by
    rintro ⟨t, N⟩
    exists (t.up 0 r.length)
    simp
    have E := r.diff_eq
    generalize r.diff = Δ at *
    clear r
    simp [E]
    apply Tm.NF.weaken_app
    exact N
  map_id {Γ: Context} := by
    rintro ⟨t, N⟩
    simp
  map_comp {Γ'' Γ' Γ: Context} := by
    rintro ⟨Δ', E'⟩ ⟨Δ, E⟩
    rintro ⟨t, N⟩
    simp_all
    congr
    omega


theorem headType_atomic {Γ t T} (N: Tm.NE Γ t T):
  N.headType = .Atom -> t = .var t.headVar
:= by
  intro E
  induction t generalizing T
  case var x =>
    simp [Tm.headVar]
  case abs =>
    cases N
  case app t1 t2 IH1 IH2 =>
    simp [Tm.NE.headType, Tm.headVar] at E
    cases N with | app N _ =>
    specialize IH1 N E
    rewrite [IH1] at N
    cases N with | var N =>
    have K: t1.headVar < Γ.length := by
      apply FinMap.lookup_some_lt N
    rewrite [FinMap.lookup_lt_some K] at N
    rewrite [E] at N
    cases N


theorem NF_singleton:
  forall x: (NF (Ty.Atom.imp .Atom)).obj [], x.val = Tm.abs (Tm.var 0)
:= by
  rintro ⟨t, N⟩
  simp
  cases N with | abs N =>
  rename_i t
  cases N with | atom N =>
  have H := N.headVar_lt
  simp at H
  have A: N.headType = .Atom := by
    simp [Tm.NE.headType]
  replace N := headType_atomic N A
  rewrite [H] at N
  simp_all


def P := NF (Ty.Atom)


def η_id: NatTrans P P where
  trans {Γ} := id
  nat {Γ' Γ} r := by
    simp


def η_trans (Γ: Context) (t: Tm): Tm :=
  match t with
  | .app (.var f) _ =>
    match Γ.lookup f with
    | some (Ty.imp (Ty.imp Ty.Atom Ty.Atom) Ty.Atom) =>
      .app (.var f) (.abs (.var 0))
    | _ => t
  | _ => t


def η: NatTrans P P where
  trans {Γ} := by
    rintro ⟨t, N⟩
    exists η_trans Γ t
    simp [η_trans]
    split
    . split
      . apply Tm.NF.atom
        apply Tm.NE.app
        . apply Tm.NE.var
          assumption
        . apply Tm.NF.abs
          apply Tm.NF.atom
          apply Tm.NE.var
          simp
      . exact N
    . exact N
  nat {Γ' Γ} r := by
    rintro ⟨t, N⟩
    simp only [P, NF]
    apply Subtype.ext
    simp
    cases t with
    | var x | abs =>
      simp [η_trans, Tm.up]
    | app t1 t2 =>
      cases t1 with
      | app | abs =>
        simp [η_trans, Tm.up]
      | var f =>
        generalize E: Γ.lookup f = T
        have K: FinMap.lookup (f + (List.length Γ' - List.length Γ)) Γ' = T := by
          rcases r with ⟨Δ, E⟩
          simp [E]
          assumption
        cases T with
        | none =>
          simp [η_trans, Tm.up, E, K]
        | some T =>
          simp [η_trans, Tm.up, E, K]
          split
          . simp [Tm.up]
          . simp [Tm.up]


def Γ := [(Ty.Atom.imp .Atom).imp .Atom]
def t := Tm.app (.var 0) (.abs $ .app (.var 1) (.abs (.var 1))) -- f (λx.(f λy.x))


theorem N: Tm.NF Γ t Ty.Atom
:= by
  unfold t Γ
  apply Tm.NF.atom
  apply Tm.NE.app
  . apply Tm.NE.var
    simp
    eq_refl
  . apply Tm.NF.abs
    apply Tm.NF.atom
    apply Tm.NE.app
    . apply Tm.NE.var
      simp
      eq_refl
    . apply Tm.NF.abs
      apply Tm.NF.atom
      apply Tm.NE.var
      simp


theorem η_trans_neq_id_lemma:
  η_trans Γ t ≠ t
:= by
  simp [η_trans, Γ, t]


theorem η_trans_neq_id:
  η.trans (Γ := Γ) ≠ η_id.trans
:= by
  intro E
  replace E := congrFun E ⟨t, N⟩
  simp [η, η_id, η_trans, t, Γ] at E
  cases E

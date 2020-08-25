inductive lev : Type 
| univ_var : ℕ → lev
| zero : lev
| S : lev → lev 
| max : lev → lev → lev 
| imax : lev → lev → lev 

namespace lev
instance : has_zero lev := ⟨lev.zero⟩

def subst : lev → ℕ → lev → lev
| (univ_var u) v l := if u = v then l else univ_var u
| 0 v l := 0
| (S l1) v l := S (subst l1 v l)
| (max l1 l2) v l := max (subst l1 v l) (subst l2 v l)
| (imax l1 l2) v l := imax (subst l1 v l) (subst l2 v l)

inductive le_add : lev → lev → ℤ → Prop 
| nonneg_of_add_nonneg {l n} : 0 ≤ n → le_add 0 l n
| le_add_of_nonneg_right {l n} : 0 ≤ n → le_add l l n
| succ_le {l l' n} : le_add l l' (n - 1) → le_add (S l) l' n
| le_succ {l l' n} : le_add l l' (n + 1) → le_add l (S l') n
| le_max {l l1 l2 n} : le_add l l1 n → le_add l (max l1 l2) n
| le_max' {l l1 l2 n} : le_add l l2 n → le_add l (max l1 l2) n
| max_le {l l1 l2 n} : le_add l1 l n → le_add l2 l n → le_add (max l1 l2) l n
| imax_zero_le {l l1 n} : le_add 0 l n → le_add (imax l1 0) l n
| imax_succ_le {l l1 l2 n} : le_add (max l1 (S l2)) l n → le_add (imax l1 (S l2)) l n
| imax_imax_le {l l1 l2 l3 n} : le_add (max (imax l1 l3) (imax l2 l3)) l n → le_add (imax l1 (imax l2 l3)) l n
| le_imax_imax {l l1 l2 l3 n} : le_add l (max (imax l1 l3) (imax l2 l3)) n → le_add l (imax l1 (imax l2 l3)) n
| imax_imax_le' {l l1 l2 l3 n} : le_add (max (imax l1 l2) (imax l1 l3)) l n → le_add (imax l1 (imax l2 l3)) l n
| le_imax_imax' {l l1 l2 l3 n} : le_add l (max (imax l1 l2) (imax l1 l3)) n → le_add l (imax l1 (imax l2 l3)) n
| le_by_cases {l l' n u} : le_add (subst l u 0) (subst l' u 0) n → 
  le_add (subst l u (S (univ_var u))) (subst l' u (S (univ_var u))) n → le_add l l' n

notation l ≤ l' + n := le_add l l' n
notation l ≤ l' := le_add l l' 0

inductive lev_def_eq : lev → lev → Prop 
| anti_symm (l l') : (l : lev) ≤ l' → l' ≤ l → lev_def_eq l l'
end lev

inductive exp : Type
| sort : lev → exp
| var : ℕ → exp
| app : exp → exp → exp
| lam : exp → exp → exp
| pi : exp → exp → exp

namespace exp
def liftn : ℕ → exp → exp
| _ e@(sort _) := e
| n e@(var m) := if m < n then e else var (m + 1)
| n (app e1 e2) := app (liftn n e1) (liftn n e2)
| n (lam A e) := lam (liftn n A) (liftn (n + 1) e)
| n (pi A e) := pi (liftn n A) (liftn (n + 1) e)

def lift : exp → exp := liftn 0

def substn (a : exp) : ℕ → exp → exp
| _ e@(sort _) := e
| n e@(var m) := if m < n then e else if m = n then lift^[n] a else exp.var (m - 1)
| n (app e₁ e₂) := app (substn n e₁) (substn n e₂)
| n (lam A e) := lam (substn n A) (substn (n + 1) e)
| n (pi A e) := pi (substn n A) (substn (n + 1) e)

def subst (e a : exp) : exp := exp.substn a 0 e
end exp

def context := list exp

open lev exp

mutual inductive has_type, def_eq
with has_type : context → exp → exp → Prop
| const {Γ α β e l} : has_type Γ α (sort l) → has_type Γ e β → has_type (α :: Γ) e β
| var {Γ α l} : has_type Γ α (sort l) → has_type (α :: Γ) (var 0) (lift α)
| univ {l} : has_type [] (sort l) (sort (S l))
| app {Γ α β e1 e2} : has_type Γ e1 (pi α β) → has_type Γ e2 α → has_type Γ (app e1 e2) (subst β e2)
| lam {Γ α β e} : has_type (α :: Γ) e β → has_type Γ (lam α e) (pi α β)
| pi {Γ α β l1 l2} : has_type Γ α (sort l1) → has_type (α :: Γ) β (sort l2) → has_type Γ (pi α β) (sort (imax l1 l2))
| def_eq_subst {Γ α β e} : has_type Γ e α → def_eq Γ α β → has_type Γ e β
with def_eq : context → exp → exp → Prop
| refl {Γ α e} : has_type Γ e α → def_eq Γ e e 
| symm {Γ e e'} : def_eq Γ e e' → def_eq Γ e' e
| trans {Γ e1 e2 e3} : def_eq Γ e1 e2 → def_eq Γ e2 e3 → def_eq Γ e1 e3
| sort_def_eq {Γ l1 l2} : lev_def_eq l1 l2 → def_eq Γ (sort l1) (sort l2)
| app_subst {Γ α β e1 e1' e2 e2'} : def_eq Γ e1 e1' → has_type Γ e1 (pi α β) → has_type Γ e1' (pi α β) → 
  def_eq Γ e2 e2' → has_type Γ e2 α → has_type Γ e2' α → def_eq Γ (app e1 e2) (app e1' e2')
| lam_subst {Γ α α' e e'} : def_eq Γ α α' → def_eq (α :: Γ) e e' → def_eq Γ (lam α e) (lam α' e')
| pi_subst {Γ α α' β β'} : def_eq Γ α α' → def_eq (α :: Γ) β β' → def_eq Γ (pi α β) (pi α' β')
| β_reduc {Γ α β e e'} : has_type (α :: Γ) e β → has_type Γ e' α → def_eq Γ (app (lam α e) e') (subst e e')
| η_reduc {Γ α β e} : has_type Γ e (pi α β) → def_eq Γ (lam α (app e (var 0))) e
| proof_irrel {Γ p h h'} : has_type Γ p (sort 0) → has_type Γ h p → has_type Γ h' p → def_eq Γ h h'

inductive is_type (Γ : context) : exp → Prop
| mk {Γ α l} : has_type Γ α (sort l) → is_type α

inductive context.ok : context → Prop
| nil : context.ok []
| cons {Γ α} : context.ok Γ → is_type Γ α → context.ok (α :: Γ)

lemma context_ok_of_has_type {Γ e α} (h : has_type Γ e α) : context.ok Γ :=
begin
  induction h,
  repeat {constructor, assumption, constructor, assumption}, 
  exact context.ok.nil,
  repeat {assumption},
  cases h_x,
  assumption,
end


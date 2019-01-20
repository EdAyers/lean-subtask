

namespace expr_zipper

@[derive decidable_eq]
meta inductive path
|app_left        (left : unit) (right : expr) : path
|app_right       (left : expr) (right : unit) : path
|lam_var_type    (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : path
|lam_body        (var_name : name) (bi : binder_info) (var_type : expr) (unique_name : name) (body : unit) : path
|pi_var_type     (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : path
|pi_body         (var_name : name) (bi : binder_info) (var_type : expr) (unique_name : name) (body : unit) : path
|elet_type       (var_name : name) (type : unit) (assignment : expr)    (body : expr) : path
|elet_assignment (var_name : name) (type : expr) (assignment : unit)    (body : expr) : path
|elet_body       (var_name : name) (type : expr) (assignment : expr)    (unique_name : name) (body : unit) : path

namespace path
  meta def as_body : path → option (name × expr × name)
  |(lam_body n bi t u ()) := some (n,t,u)
  |(pi_body n bi t u ()) := some (n,t,u)
  |(elet_body n t a u ()) := some (n,t,u)
  |_ := none
  meta def uname : path → option name := λ p, do ⟨_,_,u⟩ ← as_body p, some u
end path

open path

meta structure zipper :=
(path : list path)
(current : expr)

namespace zipper
  open path
  meta def up : zipper → option zipper
  |⟨[],                           e⟩ := none
  |⟨app_left  () a          :: p, f⟩ := some $ zipper.mk p $ expr.app f a
  |⟨app_right f  ()         :: p, a⟩ := some $ zipper.mk p $ expr.app f a
  |⟨lam_var_type vn bi vt b :: p, e⟩ := some $ zipper.mk p $ expr.lam vn bi e b
  |⟨lam_body     vn bi vt u b :: p, e⟩ := some $ zipper.mk p $ expr.lam vn bi vt $ expr.abstract_local e u 
  |⟨pi_var_type  vn bi vt b :: p, e⟩ := some $ zipper.mk p $ expr.pi vn bi e b
  |⟨pi_body      vn bi vt u b :: p, e⟩ := some $ zipper.mk p $ expr.pi vn bi vt $ expr.abstract_local e u
  |⟨elet_type       n t a b :: p, e⟩ := some $ zipper.mk p $ expr.elet n e a b
  |⟨elet_assignment n t a b :: p, e⟩ := some $ zipper.mk p $ expr.elet n t e b
  |⟨elet_body       n t a u b :: p, e⟩ := some $ zipper.mk p $ expr.elet n t a $ expr.abstract_local e u
  --|_ := undefined_core $ "malformed expression zipper"

  meta def is_top : zipper → bool |⟨[],_⟩ := tt | _ := ff
  meta def set_current : expr → zipper → zipper |e ⟨p,_⟩ := ⟨p,e⟩

  meta def map_current (f : expr → expr) : zipper → zipper |⟨p,e⟩ := ⟨p,f e⟩
  meta def tmap_current (f : expr → tactic expr) : zipper → tactic zipper |⟨p,e⟩ := zipper.mk p <$> f e

  meta def down_app_left : zipper → option zipper
  |⟨p,expr.app l r⟩ := some ⟨app_left () r :: p, l⟩
  |_ := none

  meta def down_app_right : zipper → option zipper
  |⟨p,expr.app l r⟩ := some ⟨app_right l () :: p, r⟩
  |_ := none

  private meta def get_unames : zipper → list name
  |⟨p,_⟩ := p.filter_map path.uname

  private meta def get_unique_name : expr → name
  := λ e, name.mk_numeral (unsigned.of_nat $ expr.hash e) $ name.mk_string "zipper_var" $ name.anonymous

  meta def down_lam_body : zipper → option zipper
  |⟨p,expr.lam n bi t b⟩ :=
    let u := get_unique_name b in
    some $ ⟨lam_body n bi t u () :: p, b⟩ 
  | _ := none


end zipper

/-- Expression zipper monad. -/
meta def Z (α : Type) := state_t zipper tactic α
meta instance : monad Z := state_t.monad
meta instance : alternative Z := state_t.alternative
meta instance of_tactic {α : Type} : has_coe (tactic α) (Z α) := ⟨state_t.lift⟩
-- meta instance of_option {α : Type} : has_coe (p)

meta def current : Z expr := zipper.current <$> state_t.get
private meta def map_zipper (f : zipper → zipper) : Z unit := state_t.get >>= state_t.put ∘ f
private meta def omap_zipper (f : zipper → option zipper) : Z unit := state_t.get >>= lift f >>= state_t.put
private meta def tmap_zipper (f : zipper → tactic zipper) : Z unit := state_t.get >>= lift f >>= state_t.put
meta def map_current := map_zipper ∘ zipper.map_current
meta def put : expr → Z unit := λ e, map_current $ λ _, e
meta def up : Z unit := omap_zipper $ zipper.up

meta def whnf : Z unit := tmap_zipper $ zipper.tmap_current $ tactic.whnf

end expr_zipper
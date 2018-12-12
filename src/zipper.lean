/- Expression zipper -/
import .util
namespace ez

meta inductive path
|app_left (left : unit) (right : expr) : path
|app_right (left : expr) (right : unit) : path
|lam_var_type (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : path
|lam_body (var_name : name) (bi : binder_info) (var_type : expr) (body : unit) : path
|pi_var_type (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : path
|pi_body (var_name : name) (bi : binder_info) (var_type : expr) (body : unit) : path
|elet_type (var_name : name) (type : unit) (assignment : expr) (body : expr) : path
|elet_assignment (var_name : name) (type : expr) (assignment : unit) (body : expr) : path
|elet_body (var_name : name) (type : expr) (assignment : expr) (body : unit) : path

/-- A context entry. -/
meta structure src :=
(name : name)
(type : expr)

meta structure zipper :=
(path : list path)
(ctxt : list src)
(current : expr)

meta inductive down_result
|terminal : down_result
|app (left : zipper) (right : zipper) : down_result
| lam (var_name : name) (bi : binder_info) (var_type : zipper) (body : zipper) : down_result
|  pi (var_name : name) (bi : binder_info) (var_type : zipper) (body : zipper) : down_result
|elet (var_name : name) (type : zipper) (assignment : zipper) (body : zipper) : down_result

namespace zipper
    open path
    meta def down : zipper → down_result
    |⟨p,ctxt, expr.app f a⟩ := down_result.app ⟨app_left () a :: p, ctxt, f⟩ ⟨app_right f () :: p, ctxt, a⟩
    |⟨p,ctxt, expr.lam vn bi vt b⟩ := down_result.lam vn bi ⟨lam_var_type vn bi () b :: p, ctxt, vt⟩ ⟨lam_body vn bi vt () :: p, ⟨vn,vt⟩::ctxt, b⟩
    |⟨p,ctxt, expr.pi  vn bi vt b⟩ := down_result.pi  vn bi ⟨pi_var_type  vn bi () b :: p, ctxt, vt⟩ ⟨pi_body  vn bi vt () :: p, ⟨vn,vt⟩::ctxt, b⟩
    |⟨p,ctxt, expr.elet n t a b⟩ := 
        down_result.elet n 
            ⟨elet_type n () a b :: p, ctxt, t⟩ 
            ⟨elet_assignment n t () b :: p, ctxt, a⟩ 
            ⟨elet_body n t a () :: p, ⟨n,t⟩::ctxt, b⟩ 
    |⟨p,ctxt,e⟩ := down_result.terminal
    meta def up : zipper → option zipper
    |⟨[],                            ctxt,    e⟩ := none
    |⟨app_left  () a           :: p, ctxt,    f⟩ := some $ zipper.mk p ctxt $ expr.app f a
    |⟨app_right f  ()          :: p, ctxt,    a⟩ := some $ zipper.mk p ctxt $ expr.app f a
    |⟨lam_var_type vn bi vt b  :: p, ctxt,    e⟩ := some $ zipper.mk p ctxt $ expr.lam vn bi e b
    |⟨lam_body     vn bi vt b  :: p, s::ctxt, e⟩ := some $ zipper.mk p ctxt $ expr.lam vn bi vt e 
    |⟨pi_var_type  vn bi vt b  :: p, ctxt,    e⟩ := some $ zipper.mk p ctxt $ expr.pi vn bi e b
    |⟨pi_body      vn bi vt b  :: p, s::ctxt, e⟩ := some $ zipper.mk p ctxt $ expr.pi vn bi vt e
    |⟨elet_type       n t a b  :: p, ctxt,    e⟩ := some $ zipper.mk p ctxt $ expr.elet n e a b
    |⟨elet_assignment n t a b  :: p, ctxt,    e⟩ := some $ zipper.mk p ctxt $ expr.elet n t e b
    |⟨elet_body       n t a b  :: p, s::ctxt, e⟩ := some $ zipper.mk p ctxt $ expr.elet n t a e
    |_ := undefined_core $ "malformed expression zipper"
    meta def app_left : zipper → option zipper := λ z,
    match down z with
    |down_result.app l _ := some l
    |_ := none
    end 
    meta def app_right : zipper → option zipper := λ z,
    match down z with
    |down_result.app _ r := some r
    |_ := none
    end 
    meta def unzip : zipper → expr := λ z, option.rec_on (up z) (current z) (unzip)
    meta def zip : expr → zipper := λ e, zipper.mk [] [] e
    meta def set_current : expr → zipper → zipper
    |e ⟨p,c,_⟩ := ⟨p,c,e⟩
    meta def map : (expr → expr) → zipper → zipper
    |f ⟨p,ctxt,e⟩ := ⟨p,ctxt,f e⟩
    meta def mmap {T} [monad T] : (expr → T expr) → zipper → T zipper
    |f ⟨p,ctxt,e⟩ := do e ← f e, pure ⟨p,ctxt,e⟩
    meta def depth : zipper → ℕ := list.length ∘ zipper.ctxt
    meta def unzip_with : expr → zipper → expr := λ e z, unzip $ z.set_current e
    universes u v
    /-- Helper lemma for `mk_congr` -/
    lemma eq_cc {α : Type u} {β : Type v} (F : α → β) (a₁: α)
    :  ∀ a₂ : α, a₁ = a₂ → F a₁ = F a₂ 
    := @eq.rec α a₁ (λ a, F a₁ = F a) rfl
    open tactic
    /-- Given a zipper, makes a congruence lemma at the zipper's position. Assumes that the zipper is not inside any binders (for now) -/
    meta def mk_congr (z : zipper) : tactic expr := do
        when (z.depth ≠ 0) (tactic.fail "Not implemented: congruences inside a binder"),
        let lhs := z.current,
        let lhs' := z.unzip,
        T ← infer_type lhs,
        target ← to_expr $ ```(∀ X : %%(T), (%%lhs = X) → %%(lhs') = %%(z.unzip_with $ expr.var 1)),
        tactic.fabricate (some target) (do 
            -- get_goals >>= list.mmap infer_type >>= trace,
            refine ```(@eq.rec _ %%lhs (λ X, %%(lhs') = %%(z.unzip_with $ expr.var 0)) rfl),
            -- get_goals >>= list.mmap infer_type >>= trace,
            pure ()
        ) 
        
    meta def apply_congr : (expr × expr) → zipper → tactic expr := λ ⟨rhs,pf⟩ z, do
        let lhs := z.current,
        T ← infer_type lhs,
        let lhs' := z.unzip,
        let rhs' := z.unzip_with rhs,
        target ← to_expr $ ```(%%lhs' = %%rhs'),
        tactic.fabricate (some target) (do
            refine ```(@eq.rec _ %%lhs (λ X, %%lhs' = z.unzip_with $ expr.var 0) rfl %%rhs %%pf)
        )

    private meta def is_proper (p : param_info) : bool := ¬(param_info.is_implicit p || param_info.is_inst_implicit  p || param_info.is_prop p)

    /-- Take a zipper where the current expression is a function application, and return zippers over all of the non-implicit, non-prop arguments.-/
    meta def down_proper (z : zipper) : tactic (expr × list zipper) := do
        let c := z.current,
        let f := expr.get_app_fn c,
        let args := expr.get_app_args c,
        ⟨params,result_deps⟩ ← tactic.get_fun_info f (args.length),
        let params := list.reverse params,
        ⟨zippers, _⟩ ← params.mfoldl (λ acc p, do
            let (⟨zippers,z⟩ : (list zipper) × zipper) := acc,
            z' ← app_left z,
            if is_proper p then do
                zr ← app_right z,
                pure (zr::zippers,z')
            else pure (zippers, z')) (([] : list zipper), z),
        pure (f,zippers)

end zipper


end ez
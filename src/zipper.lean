/- Expression zipper -/
import .util .rule
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
meta inductive src
|Hyp (n : name) (bi : binder_info) (type : expr) : src
|Assigned (n : name) (type : expr) (assignment : expr) : src
namespace src
    meta def type : src → expr
    |(Hyp _ _ t) := t
    |(Assigned _ t _) := t
    meta def name : src → name
    |(Hyp n _ _) := n
    |(Assigned n _ _) := n
    meta def to_local : src → tactic expr
    |(Hyp n bi t) := tactic.mk_local' n bi t
    |(Assigned n t _) := tactic.mk_local' n binder_info.default t
    meta def pis_of_ctxt : list src → expr → expr
    |[] e := e
    |((src.Hyp n bi y) :: t) e := pis_of_ctxt t $ expr.pi n bi y $ e
    |((src.Assigned n y a) :: t) e := pis_of_ctxt t $ expr.elet n y a $ e
end src

/-- 
A zipper over expressions. You can think of this as being like a 'cursor' that can move around an `expr`.
It does not replace bound variables with local constants, but instead maintains its own 'mini-context' of the binders that it is under.

Reference: [Functional Pearl - The Zipper](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf)
 -/
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
    /--Move the cursor down the expression tree.-/
    meta def down : zipper → down_result
    |⟨p,ctxt, expr.app f a⟩ := down_result.app ⟨app_left () a :: p, ctxt, f⟩ ⟨app_right f () :: p, ctxt, a⟩
    |⟨p,ctxt, expr.lam vn bi vt b⟩ := down_result.lam vn bi ⟨lam_var_type vn bi () b :: p, ctxt, vt⟩ ⟨lam_body vn bi vt () :: p, (src.Hyp vn bi vt)::ctxt, b⟩
    |⟨p,ctxt, expr.pi  vn bi vt b⟩ := down_result.pi  vn bi ⟨pi_var_type  vn bi () b :: p, ctxt, vt⟩ ⟨pi_body  vn bi vt () :: p, (src.Hyp vn bi vt)::ctxt, b⟩
    |⟨p,ctxt, expr.elet n t a b⟩ := 
        down_result.elet n 
            ⟨elet_type n () a b :: p, ctxt, t⟩ 
            ⟨elet_assignment n t () b :: p, ctxt, a⟩ 
            ⟨elet_body n t a () :: p, (src.Assigned n t a)::ctxt, b⟩ 
    |⟨p,ctxt,e⟩ := down_result.terminal
    /--Pop the cursor up the expression tree. If we are already at the top, returns `none`. [NOTE] This can throw if the zipper was not formed properly.-/
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
    meta def body : zipper → option zipper := λ z,
        match down z with
        |down_result.pi _ _ _ b := some b
        |down_result.lam _ _ _ b := some b
        |down_result.elet _ _ _ b := some b
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
    /--The number of binders above the cursor. -/
    meta def depth : zipper → ℕ := list.length ∘ zipper.ctxt
    meta def unzip_with : expr → zipper → expr := λ e z, unzip $ z.set_current e
    /--Infer the type of the subexpression at the cursor position. -/
    meta def infer_type : zipper → tactic expr := λ z, do
            ⟨ins,lcs⟩ ← list.mfoldl (λ ct s, do
                l ← src.to_local s,
                pure $ (expr.instantiate_var ct.1 l, l::ct.2)
            ) (z.current,([] : list expr)) z.ctxt,
            y ← tactic.infer_type ins,
            let y := lcs.foldl expr.abstract y,
            pure y
    /-- `with_tactic t z` will replace `z.current` with a goal and then pass that goal to the given tactic. 
    If the tactic succeeds, then the result is replaced with z.current and unzipped. -/
    meta def with_tactic : tactic unit → zipper → tactic expr := λ t z, do
        Y ← infer_type z,
        let T := src.pis_of_ctxt z.ctxt Y,
        res ← tactic.fabricate (some T) (do
            list.mfoldr (λ s _, do
                lc ← tactic.intro (src.name s),
                pure ()
            ) () z.ctxt,
            t
        ),
        abstracted ← z.ctxt.mfoldr (λ s res, expr.binding_body_all res) res,
        pure $ z.unzip_with abstracted

    --meta def unzip_lambda : name → zipper → expr := λ n e z, expr.lam n binder_info.default _ $ unzip $ z.set_current (expr.var z.depth)
    meta instance : has_to_tactic_format zipper := ⟨λ z, do
     whole ← tactic.pp $ z.unzip_with `(()),
     current ← tactic.pp z.current,
     pure $ format.highlight current format.color.blue ++ " in " ++ whole
     ⟩
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
        T ← tactic.infer_type lhs,
        target ← to_expr $ ```(∀ X : %%(T), (%%lhs = X) → %%lhs' = %%(z.unzip_with $ expr.var 1)),
        tactic.fabricate (some target) (do 
            -- get_goals >>= list.mmap infer_type >>= trace,
            refine ```(@eq.rec _ %%lhs (λ X, %%(lhs') = %%(z.unzip_with $ expr.var 0)) rfl),
            -- get_goals >>= list.mmap infer_type >>= trace,
            pure ()
        ) 
    meta def unzip_free : zipper → expr := λ z, z.unzip_with $ expr.var z.depth
    #check @eq.rec
    /-- `apply_congr (rhs,pf) z` takes the given `%%pf : %%z.current = %%rhs` and makes a congruence lemma using the given zipper.  -/
    meta def apply_congr : (expr × expr) → zipper → tactic (expr × expr) := λ ⟨rhs,pf⟩ z, do
        let lhs := z.current,
        T ← tactic.infer_type lhs,
        let lhs' := z.unzip,
        let rhs' := unzip_with rhs z,
        target ← to_expr $ ```(%%lhs' = %%rhs'),
        -- pp target >>= λ m, trace $ ("target: ":format) ++ m,
        motive ← to_expr $ @expr.lam ff `X binder_info.default (to_pexpr T) $ ```(%%lhs' = %%(z.unzip_with $ expr.var z.depth)),
        -- pp motive >>= λ m, trace $ ("motive: ":format) ++ m,
        pf' ← tactic.fabricate (some target) (do
            refine ```(@eq.rec %%T %%lhs %%motive rfl %%rhs %%pf)
        ),
        pure (rhs',pf')
    meta def apply_rule : rule → zipper → tactic rule := λ r z, do
        r ← r.head_rewrite z.current,
        (rhs', pf') ← apply_congr (r.rhs,r.pf) z,
        --tactic.infer_type pf' >>= trace,
        --trace pf',
        r' ← rule.of_prf pf',
        --trace "hello",
        pure r'

    meta def apply_conv : conv unit → zipper → conv unit := λ cnv z, do
        let lhs := z.current,
        T ← tactic.infer_type lhs,
        rhs ← mk_meta_var T,
        let lhs' := z.unzip,
        target ← to_expr $ ```(%%lhs' = %%(z.unzip_with rhs)),
        rewrite_target target,
        refine ```(@eq.rec %%T %%lhs (λ X, %%lhs' = z.unzip_with $ expr.var 0) rfl %%rhs _),
        cnv


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
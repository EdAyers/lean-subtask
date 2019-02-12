/- Expression zipper -/
import .util .rule
namespace ez
open robot

@[derive decidable_eq]
meta inductive address_item 
|app_left
|app_right
|lam_var_type
|lam_body
|pi_var_type
|pi_body
|elet_type
|elet_assignment
|elet_body
meta def address := list address_item
meta instance address.has_append : has_append address := ⟨list.append⟩
@[derive decidable_eq]
meta inductive path
|app_left        (left : unit) (right : expr) : path
|app_right       (left : expr) (right : unit) : path
|lam_var_type    (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : path
|lam_body        (var_name : name) (bi : binder_info) (var_type : expr) (body : unit) : path
|pi_var_type     (var_name : name) (bi : binder_info) (var_type : unit) (body : expr) : path
|pi_body         (var_name : name) (bi : binder_info) (var_type : expr) (body : unit) : path
|elet_type       (var_name : name) (type : unit) (assignment : expr)    (body : expr) : path
|elet_assignment (var_name : name) (type : expr) (assignment : unit)    (body : expr) : path
|elet_body       (var_name : name) (type : expr) (assignment : expr)    (body : unit) : path

meta def path.to_address_item : path → address_item
|(path.app_left _ _) := address_item.app_left
|(path.app_right _ _) := address_item.app_right
|(path.lam_var_type _ _ _ _) := address_item.lam_var_type
|(path.lam_body _ _ _ _) := address_item.lam_body
|(path.pi_var_type _ _ _ _) := address_item.pi_var_type
|(path.pi_body _ _ _ _) := address_item.pi_body
|(path.elet_type _ _ _ _) := address_item.elet_type
|(path.elet_assignment _ _ _ _) := address_item.elet_assignment
|(path.elet_body _ _ _ _) := address_item.elet_body

meta def path.to_address : list path → address := list.map path.to_address_item ∘ list.reverse

/-- A context entry. -/
@[derive decidable_eq]
meta inductive src
|Hyp      (n : name) (bi : binder_info) (type : expr)  : src
|Assigned (n : name) (type : expr) (assignment : expr) : src
-- |Meta     (n : name) (type : expr)                     : src

meta def path.to_src : path → option src
|(path.lam_body n bi y b) := some $ src.Hyp n bi y
|(path.pi_body n bi y b) := some $ src.Hyp n bi y
|(path.elet_body n y a b) := some $ src.Assigned n y a
|_ := none

meta def path.to_context : list path → list src := list.choose path.to_src

namespace src
    meta def type : src → expr
    |(Hyp _ _ t) := t
    |(Assigned _ t _) := t
    -- |(Meta _ t) := t
    meta def name : src → name
    |(Hyp n _ _) := n
    |(Assigned n _ _) := n
    -- |(Meta n _) := n
    meta def to_local : src → tactic expr
    |(Hyp n bi t) := tactic.mk_local' n bi t
    |(Assigned n t _) := tactic.mk_local' n binder_info.default t
    -- |(Meta n t) := tactic.mk_meta_var t
    -- meta def pis_of_ctxt : list src → expr → expr
    -- |[] e := e
    -- |((src.Hyp n bi y) :: t) e := pis_of_ctxt t $ expr.pi n bi y $ e
    -- |((src.Assigned n y a) :: t) e := pis_of_ctxt t $ expr.elet n y a $ e
    -- |((src.Meta n y) ::t) e := pis_of_ctxt t $ expr.pi n binder_info.default y $ e -- [HACK] what should the behaviour be here?
    meta def pexpr_pis_of_ctxt : list src → pexpr → pexpr
    |[] e := to_pexpr e
    |((src.Hyp n bi y) :: rest) e := pexpr_pis_of_ctxt rest $ @expr.pi ff n bi (to_pexpr y) $ e
    |((src.Assigned n y a) :: rest) e := pexpr_pis_of_ctxt rest $ expr.elet n (to_pexpr y) (to_pexpr a) $ e
    -- |((src.Meta n y) :: rest) e := pexpr_pis_of_ctxt rest $ expr.app (expr.lam n binder_info.default (to_pexpr y) e) pexpr.mk_placeholder
    meta def hyps_of_telescope : telescope → list src := list.map (λ ⟨n,bi,y⟩, src.Hyp n bi y)
    -- meta def mvars_of_telescope : telescope → list src := list.map (λ ⟨n,bi,y⟩, src.Meta n y)
    
    /--Aux fn for `introduce_context`.-/
    private meta def mutate : list expr → list src → tactic (list expr)
    |ctxt [] := pure ctxt
    |ctxt ((Hyp n bi y)::rest) := do
        let y := expr.instantiate_vars y ctxt,
        T ← tactic.to_expr (expr.pi n bi (to_pexpr y) $ pexpr.mk_placeholder),
        tactic.change T,
        a ← tactic.intro n,
        mutate (a::ctxt) rest
    |ctxt ((Assigned n y a)::rest) := do
        let y := expr.instantiate_vars y ctxt,
        let a := expr.instantiate_vars a ctxt,
        h ← tactic.definev n y a,
        mutate (h::ctxt) rest
    -- |ctxt ((Meta n y) :: rest) := do
    --     let y := expr.instantiate_vars y ctxt,
    --     m ← tactic.mk_meta_var y,
    --     gs ← tactic.get_goals,
    --     tactic.set_goals $ m :: gs,
    --     tactic.apply_instance <|> tactic.swap,
    --     m ← tactic.instantiate_mvars m,
    --     mutate (m::ctxt) rest
    -- /-- Take the given context and make a new tactic state.
    --     - each `Hyp` becomes a local constant, 
    --     - each `Assigned` becomes an assigned local constant 
    --     - each `Meta` becomes an mvar ([TODO] should it be a goal?)
    --     Returns `(r,hs)` where:
    --     - `r` is the result term for acheiving the given goal.
    --     - `hs` are local-consts or mvars for each element of `ctxt`.
    --     The goal of the returned tactic is to be determined.
    --       -/
    -- meta def introduce_context (ctxt : list src) : tactic (expr × list expr) := do
    --     targ ← tactic.to_expr (pexpr_pis_of_ctxt ctxt $ pexpr.mk_placeholder) tt ff,
    --     res ← tactic.mk_meta_var targ,
    --     tactic.set_goals [res],
    --     es ← mutate [] $ ctxt.reverse ,
    --     pure (res, es)
    open tactic

    -- meta def revert_aux : list expr → expr → list src → tactic (expr × list src)
    -- |[] e acc := pure (e,acc)
    -- |((expr.local_const _ pn bi y)::rest) e acc := do
    --     let s := src.Hyp pn bi (expr.abstr)
    -- meta def revert_context : list expr → expr → tactic (expr × list src)
    -- |[] e := 
        
end src

/-- 
A zipper over expressions. You can think of this as being like a 'cursor' that can move around an `expr`.
It does not replace bound variables with local constants, but instead maintains its own 'mini-context' of the binders that it is under.

Reference: [Functional Pearl - The Zipper](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf)
 -/
@[derive decidable_eq]
meta structure zipper :=
(path : list path)
-- (ctxt : list src)
(current : expr)

@[derive decidable_eq]
meta inductive down_result
|terminal : down_result
|app (left : zipper) (right : zipper) : down_result
| lam (var_name : name) (bi : binder_info) (var_type : zipper) (body : zipper) : down_result
|  pi (var_name : name) (bi : binder_info) (var_type : zipper) (body : zipper) : down_result
|elet (var_name : name) (type : zipper) (assignment : zipper) (body : zipper) : down_result

meta def down_result.children : down_result → list zipper
|(down_result.terminal) := []
|(down_result.app l r) := [l,r]
|(down_result.lam n bi vt b) := [vt,b]
|(down_result.pi n bi vt b) := [vt,b]
|(down_result.elet n t a b) := [t,a,b]

namespace zipper
    open path
    /--Move the cursor down the expression tree.-/
    meta def down : zipper → down_result
    |⟨p, expr.app f a⟩ := down_result.app ⟨app_left () a :: p,  f⟩ ⟨app_right f () :: p,  a⟩
    |⟨p, expr.lam vn bi vt b⟩ := down_result.lam vn bi ⟨lam_var_type vn bi () b :: p,  vt⟩ ⟨lam_body vn bi vt () :: p,  b⟩
    |⟨p, expr.pi  vn bi vt b⟩ := down_result.pi  vn bi ⟨pi_var_type  vn bi () b :: p,  vt⟩ ⟨pi_body  vn bi vt () :: p,  b⟩
    |⟨p, expr.elet n t a b⟩ := 
        down_result.elet n 
            ⟨elet_type n () a b :: p,  t⟩ 
            ⟨elet_assignment n t () b :: p,  a⟩ 
            ⟨elet_body n t a () :: p, b⟩ 
    |⟨p,e⟩ := down_result.terminal
    meta def down_coord : address_item → zipper → option zipper
    |(address_item.app_left)        ⟨p,expr.app f a⟩      := some ⟨app_left () a            :: p, f⟩
    |(address_item.app_right)       ⟨p,expr.app f a⟩      := some ⟨app_right f ()           :: p, a⟩
    |(address_item.lam_var_type)    ⟨p,expr.lam n bi y b⟩ := some ⟨lam_var_type n bi () b   :: p, y⟩ 
    |(address_item.lam_body)        ⟨p,expr.lam n bi y b⟩ := some ⟨lam_body n bi y ()       :: p, b⟩
    |(address_item.pi_var_type)     ⟨p,expr.pi n bi y b⟩  := some ⟨pi_var_type  n bi () b   :: p, y⟩ 
    |(address_item.pi_body)         ⟨p,expr.pi n bi y b⟩  := some ⟨pi_body  n bi y ()       :: p, b⟩
    |(address_item.elet_type)       ⟨p,expr.elet n y a b⟩ := some ⟨elet_type n () a b       :: p, y⟩ 
    |(address_item.elet_assignment) ⟨p,expr.elet n y a b⟩ := some ⟨elet_assignment n y () b :: p, a⟩ 
    |(address_item.elet_body)       ⟨p,expr.elet n y a b⟩ := some ⟨elet_body n y a ()       :: p, b⟩ 
    |_ _ := none

    meta def children : zipper → list zipper := down_result.children ∘ down

    /-- Pop the cursor up the expression tree. If we are already at the top, returns `none`. 
    [NOTE] This can throw if the zipper was not formed properly.
    -/
    meta def up : zipper → option zipper
    |⟨[],                            e⟩ := none
    |⟨app_left  () a           :: p, f⟩ := some $ zipper.mk p $ expr.app f a
    |⟨app_right f  ()          :: p, a⟩ := some $ zipper.mk p $ expr.app f a
    |⟨lam_var_type vn bi vt b  :: p, e⟩ := some $ zipper.mk p $ expr.lam vn bi e b
    |⟨lam_body     vn bi vt b  :: p, e⟩ := some $ zipper.mk p $ expr.lam vn bi vt e 
    |⟨pi_var_type  vn bi vt b  :: p, e⟩ := some $ zipper.mk p $ expr.pi vn bi e b
    |⟨pi_body      vn bi vt b  :: p, e⟩ := some $ zipper.mk p $ expr.pi vn bi vt e
    |⟨elet_type       n t a b  :: p, e⟩ := some $ zipper.mk p $ expr.elet n e a b
    |⟨elet_assignment n t a b  :: p, e⟩ := some $ zipper.mk p $ expr.elet n t e b
    |⟨elet_body       n t a b  :: p, e⟩ := some $ zipper.mk p $ expr.elet n t a e
    -- |_ := undefined_core $ "malformed expression zipper"
    meta def is_top : zipper → bool := list.empty ∘ path
    meta def top := option.repeat up
    meta def down_app_left : zipper → option zipper := down_coord address_item.app_left
    meta def down_app_right : zipper → option zipper := down_coord address_item.app_right

    meta def down_body : zipper → option zipper := λ z,
        match down z with
        |down_result.pi _ _ _ b := some b
        |down_result.lam _ _ _ b := some b
        |down_result.elet _ _ _ b := some b
        |_ := none
        end
    meta def down_var_type : zipper → option zipper := λ z,
        match down z with
        |down_result.pi _ _ y b := some y
        |down_result.lam _ _ y b := some y
        |down_result.elet _ y _ b := some y
        |_ := none
        end

    meta def down_address : address → zipper → option zipper
    |[] z := some z
    |(h::t) z := down_coord h z >>= down_address t

    meta def unzip : zipper → expr := λ z, option.rec_on (up z) (current z) (unzip)
    --meta def unzip_with_ctxt : zipper → expr × list src := λ z, option.rec_on (up z) (current z, ctxt z) unzip_with_ctxt
    meta def zip : expr → zipper := λ e, zipper.mk [] e
    meta instance : has_coe expr zipper := ⟨zip⟩
    -- meta def zip_with_ctxt : list src → expr → zipper
    -- |ctxt current := {path := [], ctxt:= ctxt, current := current}
    -- meta def zip_with_metas : telescope → expr → zipper := zip_with_ctxt ∘ src.mvars_of_telescope
    -- meta def zip_with_hyps := zip_with_ctxt ∘ src.hyps_of_telescope
    meta def set_current : expr → zipper → zipper
    |e ⟨p,_⟩ := ⟨p,e⟩
    meta def map : (expr → expr) → zipper → zipper
    |f ⟨p,e⟩ := ⟨p,f e⟩
    meta def mmap {T} [monad T] : (expr → T expr) → zipper → T zipper
    |f ⟨p,e⟩ := zipper.mk p <$> f e
    meta def address : zipper → address := path.to_address ∘ path
    meta def ctxt : zipper → list src := path.to_context ∘ path
    /--The number of binders above the cursor. -/
    meta def binder_depth : zipper → ℕ := list.length ∘ ctxt
    meta def unzip_with : expr → zipper → expr := λ e z, unzip $ z.set_current e
    meta def is_var : zipper → bool := expr.is_var ∘ current
    meta def is_constant : zipper → bool := expr.is_constant ∘ current
    /--True when the current expression does not contain local constants -/
    meta def no_locals : zipper → bool := list.empty ∘ list_local_consts ∘ current 
    meta def is_local_constant : zipper → bool := expr.is_local_constant ∘ current
    meta def is_mvar : zipper → bool := expr.is_mvar ∘ current
    meta def is_terminal : zipper → bool := λ z, z.down = down_result.terminal
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
    -- meta def with_tactic : tactic unit → zipper → tactic expr := λ t z, do
    --     gs ← tactic.get_goals,
    --     ⟨e,hs⟩ ← src.introduce_context $ z.ctxt,
    --     let current := expr.instantiate_vars z.current hs,
    --     Y ← tactic.infer_type current,
    --     tactic.change Y,
    --     t,
    --     e ← tactic.instantiate_mvars e,
    --     pure e

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
        when (z.binder_depth ≠ 0) (tactic.fail "Not implemented: congruences inside a binder"),
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
    meta def unzip_free : zipper → expr := λ z, z.unzip_with $ expr.var z.binder_depth
    /-- `apply_congr (rhs,pf) z` takes the given `%%pf : %%z.current = %%rhs` and makes a congruence lemma using the given zipper.  -/
    meta def apply_congr : (expr × expr) → zipper → tactic (expr × expr) := λ ⟨rhs,pf⟩ z, do
        let lhs := z.current,
        T ← tactic.infer_type lhs,
        let lhs' := z.unzip,
        let rhs' := unzip_with rhs z,
        target ← to_expr $ ```(%%lhs' = %%rhs'),
        -- pp target >>= λ m, trace $ ("target: ":format) ++ m,
        motive ← to_expr $ @expr.lam ff `X binder_info.default (to_pexpr T) $ ```(%%lhs' = %%(z.unzip_with $ expr.var z.binder_depth)),
        -- pp motive >>= λ m, trace $ ("motive: ":format) ++ m,
        pf' ← tactic.fabricate (some target) (do
            refine ```(@eq.rec %%T %%lhs %%motive rfl %%rhs %%pf),
            all_goals $ try $ (apply_instance <|> prop_assumption)
        ),
        pure (rhs',pf')
    


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

    meta def is_type (z : zipper) : tactic bool := expr.is_sort <$> tactic.infer_type z.current

    /-- Take a zipper where the current expression is a function application, and return zippers over all of the non-implicit, non-prop arguments.-/
    meta def down_proper (z : zipper) : tactic (expr × list zipper) := do
        let c := z.current,
        let f := expr.get_app_fn c,
        let f_name := expr.const_name f,
        -- if it is a numeral then don't expand it.
        if f_name = `bit0 ∨ f_name = `bit1 then pure (f,[]) else do
        let args := expr.get_app_args c,
        params ← (fun_info.params <$> tactic.get_fun_info f (args.length)) <|> pure [],
        let params := list.reverse params,
        ⟨zippers, _⟩ ← params.mfoldl (λ acc p, do
            let (⟨zippers,z⟩ : (list zipper) × zipper) := acc,
            z' ← down_app_left z,
            if is_proper p then do
                zr ← down_app_right z,
                --t ← is_type zr,
                --if t then pure (zippers,z') else
                pure (zr::zippers,z')
            else pure (zippers, z')) (([] : list zipper), z),
        pure (f,zippers)

    meta def fold {α} (f : α → zipper → tactic α) : α → zipper → tactic α
    | a z := do a ← f a z, z.children.mfoldl fold a

    meta def traverse {α} (f : α → zipper → tactic ( α × zipper)) : (α × zipper) → tactic (α × zipper)
    | (a,z) := do (a,z) ← f a z <|> pure (a,z),
        match down z with
        |down_result.terminal := pure (a,z)
        |(down_result.app f x) := do (a,zf) ← traverse (a,f), (a,zx) ← traverse (a,x), z ← up zx, z ← pure $ set_current (expr.app zf.current zx.current) z, pure (a,z)
        |(down_result.lam _ _ _ _) := notimpl
        |(down_result.pi _ _ _ _) := notimpl
        |(down_result.elet _ _ _ _) := notimpl
        end

    /--Traverse all of zipper.current. If `f` fails, then that branch is skipped.-/
    meta def traverse_proper {α} (f : α →  zipper → tactic α) : α → zipper → tactic α
    |a z := (do
        a ← f a z,
        --zpp ← pp z,
        --trace $ ("traverse " : format) ++ zpp,
        (_,children) ← down_proper z,
        children.mfoldl traverse_proper a)
        <|> pure a

    meta def minimal_monotone {α} (p : zipper → tactic α) : zipper → tactic (list α)
    |z := (do
        a ← p z,
        (_,children) ← down_proper z,
        kids ← list.join <$> list.mmap minimal_monotone children,
        pure $ list.cases_on kids [a] (λ _ _,kids))
        <|>  pure []

    meta def maximal_monotone {α} (p : zipper → tactic α) : zipper → tactic (list α)
    |z := (do a ← p z, pure [a]) <|> do
            (_,children) ← down_proper z,
            kids ← list.join <$> list.mmap maximal_monotone children,
            pure $ kids
    /--`find_occurences z e` finds subzippers of `z` which non-trivially unify with `e`. -/
    meta def find_occurences : zipper → expr → tactic (list zipper) := λ E e,
        maximal_monotone (λ z,
            if z.is_mvar || z.is_constant then failure
            else tactic.hypothetically' (unify e z.current) *> pure z
        ) E

    meta def has_occurences : zipper → expr → tactic bool 
    := λ z e, (bnot ∘ list.empty) <$> find_occurences z e


    
    /--`lowest_uncommon_subterms l z` finds the smallest subterms of z that are not a subterm of `l`. Subterms must include a local_const -/
    meta def lowest_uncommon_subterms (l : expr) (z : zipper) :=
        minimal_monotone (λ z, 
            if z.is_mvar || z.is_constant || z.no_locals then failure else do 
            --let o := expr.occurs z.current l,
            matches ← zipper.maximal_monotone (λ rz, (tactic.hypothetically' $ unify z.current rz.current) ) $ zipper.zip l,
            -- trace_m "lus: " $ (z,l,o, matches),
            if ¬ matches.empty then failure else pure z
        ) z

    meta def largest_common_subterms (z₁ z₂ : zipper): tactic (list zipper) :=
        list.join <$> z₁.maximal_monotone (λ z₁, 
            if z₁.is_mvar then failure else do 
            ocs ← find_occurences (z₂) z₁.current, 
            if ocs.empty then failure else pure ocs
        ) 

    private meta def count_symbols_aux : table expr → zipper → tactic (table expr)
    | acc z := do
        (f,zs) ← down_proper z,
        if expr.is_mvar f then pure acc else
        zs.mfoldl count_symbols_aux $ table.insert f acc

    meta def count_symbols : expr → tactic (table expr) := count_symbols_aux ∅ ∘ zip

    meta def does_unify (e : expr) : zipper → tactic unit
    | z := if z.is_mvar then failure else
        (tactic.hypothetically' $ unify e z.current)

    meta def find_subterms (e : expr) : zipper → tactic (list zipper)
    := traverse_proper (λ acc z, (does_unify e z *> pure (z::acc)) <|> pure acc) []

    meta def has_single_subterm (e : expr) : zipper → tactic (zipper)
    := λ z, do [x] ← find_subterms e z, pure x

    meta def count_subterms (e : expr) : zipper → tactic ℕ
    := λ z, do xs ← find_subterms e z, pure $ list.length xs

    meta def find_subterm (e : expr) : zipper → tactic zipper
    |z :=
        (does_unify e z *> pure z)
        <|> do 
            (_,zs) ← down_proper z,
            list.mfirst find_subterm zs

    meta def distance_to_subterm_down (e : expr) : zipper → nat → tactic nat
    |z d :=
        if z.is_mvar then failure else
        (tactic.hypothetically' $ (do 
            unify e z.current,  pure d
        ))
        <|> (do
            -- tactic.trace_m "dtsd: " $ z,
            (_,zs) ← down_proper z,
            list.mfirst (λ iz : ℕ × zipper, distance_to_subterm_down iz.2 $ iz.1 + d + 1)
            $ list.with_indices zs
        )

    meta def is_app_right : zipper → bool
    |⟨(path.app_right _ _)::t,_⟩ := tt
    |_ := ff

    meta def right : zipper → option zipper
    |z := if is_app_right z then up z >>= right else up z >>= down_app_right

    meta def distance_to_subterm_up (e : expr) : ℕ → zipper → tactic ℕ
    |d z :=
        if is_app_right z then up z >>= distance_to_subterm_up (d+1) else do
        -- tactic.trace_m "dtsu1: " $ z,
        z ← up z >>= lift down_app_right,
        -- tactic.trace_m "dtsu2: " $ z,
        distance_to_subterm_down e z (d+1) 
        <|> distance_to_subterm_up (d+1) z

    meta def get_distance (outer : expr) (l : expr) (r : expr) : tactic ℕ := do
        outer ← instantiate_mvars outer,
        first ← find_subterm l outer,
        -- tactic.trace_m "gd: " $ first, 
        distance_to_subterm_up r 0 first

    meta def get_proper_children (e : expr) : tactic (list expr) := do
        e ← instantiate_mvars e,
        (list.map current <$> prod.snd <$> (down_proper $ zip e)) <|> pure []
    meta def get_smallest_complex_subterms (z : zipper) : tactic (list zipper) := do
        minimal_monotone (λ z, do ⟨_,[]⟩ ← down_proper z | failure, pure z) z

    meta def instantiate_mvars : zipper → tactic zipper
    |z := do
        let a := address z,
        let e := unzip z,
        e ← tactic.instantiate_mvars e,
        z ← down_address a e,
        pure z

    -- meta def clone_mvars : zipper → tactic (zipper)
    -- |z := do 
    --     (a,z) ← zipper.traverse (λ (t:dict name expr) z, _) (∅,z) ,
    --     sorry

    -- meta def unify (l : zipper) (r : zipper) : tactic unit := do 
    --     hypothetically (do
    --         l_ctxt ← src.intro_ctxt [] $ l.ctxt.reverse,
    --         r_ctxt ← src.intro_ctxt [] $ r.ctxt.reverse,
    --         lc ← pure $ expr.instantiate_vars l.current l_ctxt,
    --         rc ← pure $ expr.instantiate_vars r.current r_ctxt,
    --         tactic.unify lc rc,
    --         -- now some of the metavariables in l_ctxt and r_ctxt will be assigned.
    --         -- also note that these assignments can depend on other non-assigned metavariables.
    --         -- [FIXME] for now, we ignore this case and assume that the metas are never assigned wrt other metas.
    --         expr.a
    --     )

    -- /-- `match_current e z` tries to match `e` with `z.current` in `z`'s context. 
    --     Recall that _matching_ is distinct from _unifying_ in that only metavariables in `z.current` may be assigned from this process.
    --     So if `z.ctxt` has metavariables, these can be assigned. -/
    -- meta def match_current : expr → zipper → tactic zipper | e z := do
    --     -- [HACK] for now, assume that the zipper's context is composed entirely of metas.
    --     T ← tactic.infer_type e,
    --     current ← tactic.to_expr $ src.pexpr_pis_of_ctxt z.ctxt (to_pexpr z.current),
    --     tactic.unify e current,

    --     let c := z.current,
    --     let t := z.ctxt.reverse,
        
    --     notimpl

end zipper

end ez
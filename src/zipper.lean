/- Expression zipper -/
import .util .rule
namespace ez
open robot

/-- Labels for each recursive argument of a constructor for `expr`. -/
@[derive decidable_eq]
meta inductive coord 
|app_left     |app_right
|lam_var_type |lam_body
|pi_var_type  |pi_body
|elet_type    |elet_assignment |elet_body
meta def coord.code: coord → ℕ |coord.app_left          := 0 |coord.app_right         := 1 |coord.lam_var_type      := 2 |coord.lam_body          := 3 |coord.pi_var_type       := 4 |coord.pi_body           := 5 |coord.elet_type         := 6 |coord.elet_assignment   := 7 |coord.elet_body         := 8
meta instance coord.has_lt : has_lt coord := ⟨λ x y, x.code < y.code⟩
meta instance coord.dec_lt : decidable_rel ((<) : coord → coord → Prop) := by apply_instance
/-- A list of `coord`s, specifying a position in an expression. The first coordinate says which way to go on the root.-/
meta def address := list coord
meta instance address.has_lt : has_lt address := show has_lt (list coord), by apply_instance
meta instance address.dec_lt : decidable_rel ((<) : address → address → Prop) := by apply_instance
meta instance address.has_append : has_append address := ⟨list.append⟩
/-- `is_below x y` is true when `∃ z, y ++ z = x` -/
meta def address.is_below : address → address → bool
|_ [] := tt -- everything is below root.
|[] _ := ff -- root is below nothing but itself.
|(h₁ :: t₁) (h₂ :: t₂) := h₁ = h₂ ∧ address.is_below t₁ t₂
infixr  ` ≺ `:50 := address.is_below
/-- A path is the part of the zipper that remembers the stuff above the zipper's cursor.-/
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

meta def path.to_coord : path → coord
|(path.app_left _ _)            := coord.app_left
|(path.app_right _ _)           := coord.app_right
|(path.lam_var_type _ _ _ _)    := coord.lam_var_type
|(path.lam_body _ _ _ _)        := coord.lam_body
|(path.pi_var_type _ _ _ _)     := coord.pi_var_type
|(path.pi_body _ _ _ _)         := coord.pi_body
|(path.elet_type _ _ _ _)       := coord.elet_type
|(path.elet_assignment _ _ _ _) := coord.elet_assignment
|(path.elet_body _ _ _ _)       := coord.elet_body

meta def path.to_address : list path → address := list.map path.to_coord ∘ list.reverse

/-- A context entry for the zipper's cursor. 
In the current implementation; as zippers traverse below lambdas, 
pis and elets, they don't replace de-Bruijn indices with local constants.
 -/
@[derive decidable_eq]
meta inductive src
|Hyp      (n : name) (bi : binder_info) (type : expr)  : src
|Assigned (n : name) (type : expr) (assignment : expr) : src

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
    meta def name : src → name
    |(Hyp n _ _) := n
    |(Assigned n _ _) := n
    meta def to_local : src → tactic expr
    |(Hyp n bi t) := tactic.mk_local' n bi t
    |(Assigned n t _) := tactic.mk_local' n binder_info.default t
    meta def pexpr_pis_of_ctxt : list src → pexpr → pexpr
    |[] e := to_pexpr e
    |((src.Hyp n bi y) :: rest) e := pexpr_pis_of_ctxt rest $ @expr.pi ff n bi (to_pexpr y) $ e
    |((src.Assigned n y a) :: rest) e := pexpr_pis_of_ctxt rest $ expr.elet n (to_pexpr y) (to_pexpr a) $ e
    meta def hyps_of_telescope : telescope → list src := list.map (λ ⟨n,bi,y⟩, src.Hyp n bi y)
end src

/-- 
A zipper over expressions. You can think of this as being like a 'cursor' that can move around an `expr`.
It does not replace bound variables with local constants, but instead maintains its own 'mini-context' of the binders that it is under.

Reference: [Functional Pearl - The Zipper](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf)
 -/
@[derive decidable_eq]
meta structure zipper :=
(path : list path)
(current : expr)

/-- Result type of calling `zipper.down`.  -/
@[derive decidable_eq]
meta inductive down_result
|terminal : down_result
|app  (left : zipper) (right : zipper) : down_result
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
    |⟨p, expr.app f a⟩ := 
        down_result.app 
            ⟨app_left  () a  :: p, f⟩ 
            ⟨app_right f  () :: p, a⟩
    |⟨p, expr.lam n bi y b⟩ := 
        down_result.lam n bi 
            ⟨lam_var_type n bi () b  :: p, y⟩ 
            ⟨lam_body     n bi y  () :: p, b⟩
    |⟨p, expr.pi  n bi y b⟩ := 
        down_result.pi n bi 
            ⟨pi_var_type  n bi () b  :: p,  y⟩
            ⟨pi_body      n bi y  () :: p,  b⟩
    |⟨p, expr.elet n t a b⟩ := 
        down_result.elet n 
            ⟨elet_type n () a b :: p,  t⟩ 
            ⟨elet_assignment n t () b :: p,  a⟩ 
            ⟨elet_body n t a () :: p, b⟩ 
    |⟨p,e⟩ := down_result.terminal
    meta def children : zipper → list zipper := down_result.children ∘ down

    meta def down_coord : coord → zipper → option zipper
    |(coord.app_left)        ⟨p,expr.app f a⟩      := some ⟨app_left  () a           :: p, f⟩
    |(coord.app_right)       ⟨p,expr.app f a⟩      := some ⟨app_right f ()           :: p, a⟩
    |(coord.lam_var_type)    ⟨p,expr.lam n bi y b⟩ := some ⟨lam_var_type n bi () b   :: p, y⟩ 
    |(coord.lam_body)        ⟨p,expr.lam n bi y b⟩ := some ⟨lam_body     n bi y ()   :: p, b⟩
    |(coord.pi_var_type)     ⟨p,expr.pi n bi y b⟩  := some ⟨pi_var_type  n bi () b   :: p, y⟩ 
    |(coord.pi_body)         ⟨p,expr.pi n bi y b⟩  := some ⟨pi_body      n bi y ()   :: p, b⟩
    |(coord.elet_type)       ⟨p,expr.elet n y a b⟩ := some ⟨elet_type       n () a b :: p, y⟩ 
    |(coord.elet_assignment) ⟨p,expr.elet n y a b⟩ := some ⟨elet_assignment n y () b :: p, a⟩ 
    |(coord.elet_body)       ⟨p,expr.elet n y a b⟩ := some ⟨elet_body       n y a () :: p, b⟩ 
    |_ _ := none

    /-- Pop the cursor up the expression tree. If we are already at the top, returns `none`. -/
    meta def up : zipper → option zipper
    |⟨[],                            e⟩ := none
    |⟨app_left  () a           :: p, f⟩ := some $ zipper.mk p $ expr.app f a
    |⟨app_right f  ()          :: p, a⟩ := some $ zipper.mk p $ expr.app f a
    |⟨lam_var_type   n bi _ b  :: p, e⟩ := some $ zipper.mk p $ expr.lam n bi e b
    |⟨lam_body       n bi y _  :: p, e⟩ := some $ zipper.mk p $ expr.lam n bi y e 
    |⟨pi_var_type    n bi _ b  :: p, e⟩ := some $ zipper.mk p $ expr.pi  n bi e b
    |⟨pi_body        n bi y _  :: p, e⟩ := some $ zipper.mk p $ expr.pi  n bi y e
    |⟨elet_type       n _ a b  :: p, e⟩ := some $ zipper.mk p $ expr.elet n e a b
    |⟨elet_assignment n t _ b  :: p, e⟩ := some $ zipper.mk p $ expr.elet n t e b
    |⟨elet_body       n t a _  :: p, e⟩ := some $ zipper.mk p $ expr.elet n t a e
    meta def is_top : zipper → bool := list.empty ∘ path
    meta def top := option.repeat up
    meta def down_app_left : zipper → option zipper := down_coord coord.app_left
    meta def down_app_right : zipper → option zipper := down_coord coord.app_right

    meta def down_body : zipper → option zipper := λ z,
        match down z with
        |down_result.pi   _ _ _ b := some b
        |down_result.lam  _ _ _ b := some b
        |down_result.elet _ _ _ b := some b
        |_ := none
        end
    meta def down_var_type : zipper → option zipper := λ z,
        match down z with
        |down_result.pi   _ _ y b := some y
        |down_result.lam  _ _ y b := some y
        |down_result.elet _ y _ b := some y
        |_ := none
        end
    /-- Move the cursor down according to the given address. 
    If the zipper has the wrong structure then return none.-/
    meta def down_address : address → zipper → option zipper
    |[]     z := some z
    |(h::t) z := down_coord h z >>= down_address t

    meta def unzip : zipper → expr := λ z, option.rec_on (up z) (current z) (unzip)
    meta def zip : expr → zipper := λ e, zipper.mk [] e
    meta instance : has_coe expr zipper := ⟨zip⟩
    meta def set_current : expr → zipper → zipper
    |e ⟨p,_⟩ := ⟨p,e⟩
    /-- Map the current subexpression. -/
    meta def map : (expr → expr) → zipper → zipper
    |f ⟨p,e⟩ := ⟨p,f e⟩
    meta def mmap {T} [monad T] : (expr → T expr) → zipper → T zipper
    |f ⟨p,e⟩ := zipper.mk p <$> f e
    meta def address : zipper → address := path.to_address ∘ path
    meta def ctxt : zipper → list src := path.to_context ∘ path
    /-- The number of binders above the cursor. -/
    meta def binder_depth : zipper → ℕ := list.length ∘ ctxt
    /-- Replace the current subexpression and unzip. -/
    meta def unzip_with : expr → zipper → expr := λ e z, unzip $ z.set_current e
    meta def is_var : zipper → bool := expr.is_var ∘ current
    meta def is_constant : zipper → bool := expr.is_constant ∘ current
    /--True when the current expression does not contain local constants -/
    meta def no_local_consts : zipper → bool := list.empty ∘ list_local_consts ∘ current 
    meta def no_local_const_terms : zipper → tactic bool := λ z, list.empty <$> (list_local_const_terms $ current $ z)
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
    /-- Given a zipper, makes a congruence lemma at the zipper's position. 
    [NOTE] Assumes that the zipper is not inside any binders (for now). -/
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
    /-- Replace the current expression with an unbound deBruijn variable. -/
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
    
    /-- Produce a conversion that uses the given conversion at the zipper's subexpression.-/
    meta def apply_conv : conv unit → zipper → conv unit := λ cnv z, do
        let lhs := z.current,
        T ← tactic.infer_type lhs,
        rhs ← mk_meta_var T,
        let lhs' := z.unzip,
        target ← to_expr $ ```(%%lhs' = %%(z.unzip_with rhs)),
        rewrite_target target,
        refine ```(@eq.rec %%T %%lhs (λ X, %%lhs' = z.unzip_with $ expr.var 0) rfl %%rhs _),
        cnv

    /-- A proper argument is one who is not implicit or a proposition.
        Ie, anything which the user would see when writing down the term. -/
    private meta def is_proper (p : param_info) : bool := 
        ¬(param_info.is_implicit p || param_info.is_inst_implicit  p || param_info.is_prop p)

    meta def is_type (z : zipper) : tactic bool := expr.is_sort <$> tactic.infer_type z.current

    /-- Take a zipper where the current expression is a function application, 
        and return zippers over all of the non-implicit, non-prop arguments. -/
    meta def down_proper (z : zipper) : tactic (zipper × list zipper) := do
        let c := z.current,
        let f := expr.get_app_fn c,
        let f_name := expr.const_name f,
        -- if it is a numeral then don't expand it.
        if f_name = `bit0 ∨ f_name = `bit1 then pure (z,[]) else do
        let args := expr.get_app_args c,
        params ← (fun_info.params <$> tactic.get_fun_info f (args.length)) <|> pure [],
        let params := list.reverse params,
        ⟨zippers, fz⟩ ← params.mfoldl (λ acc p, do
                let (⟨zippers,z⟩ : (list zipper) × zipper) := acc,
                z' ← down_app_left z,
                if is_proper p then do
                    zr ← down_app_right z,
                    --t ← is_type zr,
                    --if t then pure (zippers,z') else
                    pure (zr::zippers,z')
                else pure (zippers, z')
            ) 
            (([] : list zipper), z),
        pure (fz,zippers)

    meta def fold {α} (f : α → zipper → α) : α → zipper → α
    | a z := z.children.foldl fold $ f a z
    meta def mfold {T} [monad T] {α} (f : α → zipper → T α) : α → zipper → T α
    | a z := do a ← f a z, z.children.mfoldl mfold a

    /-- Traverse zipper.current, only exploring explicit, non-Prop arguments.
        If `f` fails, then that branch is skipped. -/
    meta def traverse_proper {α} (f : α →  zipper → tactic α) : α → zipper → tactic α
    |a z := (do
        a ← f a z,
        (_,children) ← down_proper z,
        children.mfoldl traverse_proper a)
        <|> pure a

    /-- `minimal_monotone p z` finds the smallest proper subexpressions of the zipper such that 
        `p` doesn't fail. 
        [NOTE] It assumes that if `p e` fails, then all of `e`s subexpressions will fail too. -/
    meta def minimal_monotone {α} (p : zipper → tactic α) : zipper → tactic (list α)
    |z := (do
            a ← p z,
            (_,children) ← down_proper z,
            kids ← list.join <$> list.mmap minimal_monotone children,
            pure $ list.cases_on kids [a] (λ _ _,kids)
        )
        <|>  pure []

    /-- `maximal_monotone p z`: Find the largest proper subexpressions of the zipper such that 
        `p` doesn't fail. 
        [NOTE] It assumes that if `p e` fails, then all of `e`s subexpressions will fail too. -/
    meta def maximal_monotone {α} (p : zipper → tactic α) : zipper → tactic (list α)
    |z := (do a ← p z, pure [a]) <|> do
            (f,children) ← down_proper z,
            children ← pure $ if is_local_constant f && ¬children.empty then f :: children else children,
            kids ← list.join <$> list.mmap maximal_monotone children,
            pure $ kids
    /-- `find_occurences z e` finds subexpressions of `z` which non-trivially unify with `e`. -/
    meta def find_occurences : zipper → expr → tactic (list zipper) := λ E e,
        maximal_monotone (λ z,
            if z.is_mvar || z.is_constant then failure
            else tactic.hypothetically' (unify e z.current) *> pure z
        ) E

    meta def has_occurences : zipper → expr → tactic bool 
    := λ z e, (bnot ∘ list.empty) <$> find_occurences z e

    meta def smallest_absent_subterms_aux (l : expr) (filter : zipper → tactic bool := combinator.K $ pure tt) : list ez.address  → zipper → tactic (list ez.address × list (ℕ × zipper))
    |used z := do
        filt ← filter z, 
        if ¬ filt then pure (used, []) else do
        occs ← find_occurences l z.current,
        o ← pure $ list.first (λ o, bnot $ list.any used $ λ x, zipper.address o ≺ x) occs,
        match o with
        |none := do -- z.current is not present, descend.
            (_,children) ← down_proper z,
            (used,zs) ← list.mfoldl (λ p child, do 
                (used,zs') ← smallest_absent_subterms_aux (prod.fst p) child, 
                pure (used,zs' ++ p.2)
            ) (used,[]) children,
            if zs.empty then pure $ (used,[(occs.length + 1,z)]) else pure $ (used,zs)
        |some o := 
            -- z.current is present on the lhs
            -- so now we need to add `o` to the used list so that later matches can't use it.
            pure $ (used.insert o.address,[])
        end
    
    /-- find subterms of RHS that do not appear on LHS. It will also count when occurrences have been used.
        So for example, ``smallest_absent_subterms `(a * b + b * a) `(a * b + a * b)`` will return `[(2,a * b)] because
        `a * b` occurs once in the LHS but twice in the RHS. 
    -/
    meta def smallest_absent_subterms (lhs : expr) (rhs : zipper) :=
        prod.snd <$> smallest_absent_subterms_aux lhs (λ z, bnot <$> no_local_const_terms z) [] rhs

    meta def smallest_absent_composite_subterms (lhs : expr) (rhs : zipper) :=
        prod.snd 
            <$> smallest_absent_subterms_aux lhs 
                (λ s, pure $ expr.is_composite s.current) 
                [] rhs

    /--`lowest_uncommon_subterms l z` finds the smallest subterms of z that are not a subterm of `l`. Subterms must include a local_const -/
    meta def lowest_uncommon_subterms (l : expr) (z : zipper) :=
        minimal_monotone (λ z,
            if z.is_mvar || z.is_constant || z.no_local_consts then failure else do 
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
        if zipper.is_mvar f then pure acc else
        zs.mfoldl count_symbols_aux $ table.insert f.current acc

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
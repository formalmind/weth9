import Specs.WETH9

open FormalAst

/-- `WETH9.totalSupply` never reverts, writes no storage, and returns `address(this).balance`. -/
theorem WETH9.totalSupply_spec {σ : Type} (ext : Ext σ) (env : Env) (s : σ) :
    ((WETH9.totalSupply ext).run env).run s = .ok (env.balance, s) := rfl

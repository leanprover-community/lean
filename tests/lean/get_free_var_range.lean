-- should be 0
#eval expr.get_free_var_range `(Type)
-- should be 2
#eval expr.get_free_var_range (expr.lam `hello binder_info.default `(Type) $ expr.app (expr.var 1) (expr.var 2))
-- should be 3
#eval expr.get_free_var_range (expr.app (expr.var 1) (expr.var 2))
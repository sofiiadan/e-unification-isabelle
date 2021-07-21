structure Utils =
struct

fun pretty_helper_p aux prems =
  prems |> map aux
        |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
        |> Pretty.enum "," "[" "]"

fun pretty_prems ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt)
  in pretty_helper_p (print o get_trms) env
end

fun pretty_hint ctxt (_,prems,thm) =
  Pretty.block
    [pretty_prems ctxt prems, Pretty.str " \<Longrightarrow> ", Syntax.pretty_term ctxt (Thm.concl_of thm)]

fun tracing_hint ctxt = (tracing o Pretty.string_of o pretty_hint ctxt)

fun tracing_str_hint ctxt str h = tracing (str ^ (Pretty.string_of (pretty_hint ctxt h)))

fun print_matched_hint ctxt (t1,t2,thm) =
  "Terms "
    ^ Pretty.string_of (pretty_term ctxt t1) ^ ", "
    ^ Pretty.string_of (pretty_term ctxt t2) ^ " matched hint: "
    ^ Pretty.string_of (pretty_thm ctxt thm)

fun print_matching_hints ctxt hs =
  let val _ = tracing "This hint matched but the resulting unification could not be solved:"
  in fold (fn ((t1,t2),(_,_,thm),exn) => fn _ =>
        (tracing (print_matched_hint ctxt (t1,t2,thm));
         Log.debug ctxt (tracing o (fn str => "Exception raised:\n"^str) o @{make_string}) exn)) hs ()
  end

end

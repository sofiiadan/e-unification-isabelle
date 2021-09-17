\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Logging\<close>
theory Logging
imports Pure
keywords "config" :: thy_decl
begin
paragraph \<open>Summary\<close>
text \<open>Generic logging inspired by Apache's Log4J 2
🌐\<open>https://logging.apache.org/log4j/2.x/manual/customloglevels.html\<close>
\<close>

ML_file\<open>logger.ML\<close>
ML_file\<open>antiquotations.ML\<close>

(*the root logger*)
ML\<open>
  structure Logger = @{new_logger "root"}
  structure Root_Logger = Logger
\<close>

(*set up the config command*)
ML\<open>
val _ =
  let
    fun put_configs (options, pos) =
      let
        fun put_config_of ((c, _), (v, _)) = "Config.put_global (" ^ c ^ ") (" ^ v ^ ")"
        val put_configs_string =
          fold_rev (fn c => fn acc => put_config_of c :: acc) options []
          |> String.concatWith " #> "
      in
        ML_Context.expression pos (ML_Lex.read ("val _ = Theory.setup (" ^ put_configs_string ^ ")"))
        |> Context.theory_map
      end
  in
    Outer_Syntax.command @{command_keyword "config"} "set configuration"
      (Parse.position Parse.options >> (Toplevel.theory o put_configs))
  end
\<close>

end

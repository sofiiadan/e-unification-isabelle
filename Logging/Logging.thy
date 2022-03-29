\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Logging\<close>
theory Logging
imports Pure
keywords "config" :: thy_decl
begin
paragraph \<open>Summary\<close>
text \<open>Generic logging inspired by Apache's Log4J 2
\<^url>\<open>https://logging.apache.org/log4j/2.x/manual/customloglevels.html\<close>
\<close>

ML_file\<open>logger.ML\<close>
ML_file\<open>antiquotations.ML\<close>

text\<open>Set up the root logger\<close>
ML\<open>
  structure Logger = @{new_logger "root"}
  structure Root_Logger = Logger
\<close>

text\<open>Set up the config command\<close>
ML\<open>
val _ =
  let
    fun put_configs (options, range) =
      let
        fun put_config_of ((c, _), (v, _)) = "Config.put_generic (" ^ c ^ ") (" ^ v ^ ")"
        val put_configs_string =
          fold_rev (fn c => fn acc => put_config_of c :: acc) options []
          |> String.concatWith " #> "
        val decl = "fn _ => (" ^ put_configs_string ^ ")"
      in
        Isar_Cmd.declaration {syntax = false, pervasive = false} (Input.source false decl range)
      end
  in
    Outer_Syntax.local_theory @{command_keyword "config"} "set configurations"
      (Parse.range Parse.options >> put_configs)
  end
\<close>

end

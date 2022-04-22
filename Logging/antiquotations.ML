(*  Title:      Logging/antiquotations.ML
    Author:     Kevin Kappelmann
*)
signature LOGGING_ANTIQUOTATIONS =
sig
  val show_pos: bool Config.T
end

structure Logging_Antiquotations : LOGGING_ANTIQUOTATIONS =
struct

val show_pos = Attrib.setup_config_bool @{binding "log_show_pos"} (K false)

val log =
  let
    val scan_default = Scan.lift o Scan.optional Args.name
    val scan_option = Scan.lift (Scan.option Args.name)
    fun info show_pos pos = String.concat [
        "(if (", show_pos, ") then ",
          "\"\\n\" ^ (Position.here (", ML_Syntax.print_position pos, "))",
        "else \"\")"
      ]
    fun body ts (((log_level, logger), output_opt), show_pos_opt) ctxt =
      let
        val output = the_default ("Root_Logger.default_output " ^ log_level) output_opt
        val show_pos = the_default ("Config.get ctxt Logging_Antiquotations.show_pos") show_pos_opt
        val info = info show_pos (Token.pos_of (hd ts))
        val code = String.concat [
            "(fn ctxt => fn message_f => ", logger, ".log ctxt (", log_level, ") ",
            "(", output, ") (fn _ => message_f () ^ ", info, "))"
          ]
      in (K ("", code), ctxt) end
  in
    (*use `declaration` rather than `inline` because `declaration` passes the token list, which can
      be used to retrieve a position even when no arguments are passed to the scanner*)
    ML_Antiquotation.declaration @{binding "log"}
      (scan_default "Root_Logger.INFO" -- scan_default "Logger" -- scan_option -- scan_option)
      body
  end

val new_logger = ML_Antiquotation.inline @{binding "new_logger"}
  (Scan.lift Args.name_position >>
    (fn (name, pos) => cat_lines [
      "Logger(struct val name = \"" ^ name ^ "\"",
      "val pos = " ^ ML_Syntax.print_position pos ^ "; end)"
    ]))

(*setup the antiquotations*)
val _ = Theory.setup (
    log #>
    new_logger
  )

end
(*  Title:      Logging/logger.ML
    Author:     Kevin Kappelmann, Paul Bachmann

A basic generic logger. The log levels are based on Apache's Log4J 2
https://logging.apache.org/log4j/2.x/manual/customloglevels.html
*)
signature LOGGER =
sig
  type log_level
  val OFF   : log_level
  val FATAL : log_level
  (*error log level*)
  val ERR   : log_level
  val WARN  : log_level
  val INFO  : log_level
  val DEBUG : log_level
  val TRACE : log_level
  val ALL   : log_level
  val log_level_config : log_level Config.T

  (*prints message created by passed function to passed channel if the context's
    current log_level is greater or equal than the passed level; uses lazy
    computation of the message to avoid computations in case the current log
    level blocks printing of the message.*)
  val log : Proof.context -> log_level -> ('a -> unit) -> (unit -> 'a) -> unit

  val default_output : log_level -> (string -> unit)

  (* logging functions for different log levels *)

  val fatal : Proof.context -> ('a -> unit) -> (unit -> 'a) -> unit
  val fatal' : Proof.context -> (unit -> string) -> unit

  val err : Proof.context -> ('a -> unit) -> (unit -> 'a) -> unit
  val err' : Proof.context -> (unit -> string) -> unit

  val warn : Proof.context -> ('a -> unit) -> (unit -> 'a) -> unit
  val warn' : Proof.context -> (unit -> string) -> unit

  val info : Proof.context -> ('a -> unit) -> (unit -> 'a) -> unit
  val info' : Proof.context -> (unit -> string) -> unit

  val debug : Proof.context -> ('a -> unit) -> (unit -> 'a) -> unit
  val debug' : Proof.context -> (unit -> string) -> unit

  val trace : Proof.context -> ('a -> unit) -> (unit -> 'a) -> unit
  val trace' : Proof.context -> (unit -> string) -> unit
end

functor Logger(P : sig
    val name : bstring
    val pos: Position.T
  end) : LOGGER =
struct

type log_level = int
(*values for different log levels*)
val OFF = 0
val FATAL = 100
val ERR = 200
val WARN = 300
val INFO = 400
val DEBUG = 500
val TRACE = 600
val ALL = 1000

(*setup config value log_level_<P.name>, e.g. log_level_unifier*)
val log_level_config =
  Attrib.setup_config_int (Binding.make ("log_level_" ^ P.name, P.pos)) (K INFO)

fun log ctxt log_level print_f message_f =
  if log_level <= Config.get ctxt log_level_config then print_f (message_f ())
  else ()

fun default_output log_level =
  if log_level <= WARN then warning
  else if log_level < TRACE then writeln
  else tracing

fun fatal ctxt = log ctxt FATAL
fun fatal' ctxt = log ctxt FATAL warning

fun err ctxt = log ctxt ERR
fun err' ctxt = log ctxt ERR warning

fun warn ctxt = log ctxt WARN
fun warn' ctxt = log ctxt WARN warning

fun info ctxt = log ctxt INFO
fun info' ctxt = log ctxt INFO writeln

fun debug ctxt = log ctxt DEBUG
fun debug' ctxt = log ctxt DEBUG writeln

fun trace ctxt = log ctxt TRACE
fun trace' ctxt = log ctxt TRACE tracing

end

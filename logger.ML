(*  Title:      Unification_Hints/logger.ML
    Author:     Paul Bachmann

A basic generic logger. The log levels are based on Apache's Log4J 2
https://logging.apache.org/log4j/2.x/manual/customloglevels.html
*)
signature LOGGER =
sig
  type loglevel
  val OFF   : loglevel
  val FATAL : loglevel
  (*error log level*)
  val ERR   : loglevel
  val WARN  : loglevel
  val INFO  : loglevel
  val DEBUG : loglevel
  val TRACE : loglevel
  val ALL   : loglevel
  val log_level_config : loglevel Config.T
  (*general logging function; prints message using print_f if current log_level \<ge> lvl*)
  val log : Proof.context -> loglevel -> ('a -> unit) -> 'a -> unit
  (* logging functions for different log levels *)
  val fatal : Proof.context -> ('a -> unit) -> 'a -> unit
  val err : Proof.context -> ('a -> unit) -> 'a -> unit
  val warn : Proof.context -> ('a -> unit) -> 'a -> unit
  val info : Proof.context -> ('a -> unit) -> 'a -> unit
  val debug : Proof.context -> ('a -> unit) -> 'a -> unit
  val trace : Proof.context -> ('a -> unit) -> 'a -> unit
end

structure Logger : LOGGER =
struct

type loglevel = int
(*values for different log levels*)
val OFF   = 0
val FATAL = 100
val ERR   = 200
val WARN  = 300
val INFO  = 400
val DEBUG = 500
val TRACE = 600
val ALL   = 1000

(*setup for config value log_level*)
val log_level_config = Attrib.setup_config_int \<^binding>\<open>log_level\<close> (K INFO)

fun log ctxt log_level print_f =
  if log_level < Config.get ctxt log_level_config then print_f else K ()

fun fatal ctxt = log ctxt FATAL
fun err ctxt = log ctxt ERR
fun warn ctxt = log ctxt WARN
fun info ctxt = log ctxt INFO
fun debug ctxt = log ctxt DEBUG
fun trace ctxt = log ctxt TRACE

end

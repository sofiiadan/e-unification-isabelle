signature LOG = 
sig
  type loglevel
  val OFF   : loglevel
  val FATAL : loglevel
  val ERR   : loglevel
  val WARN  : loglevel
  val INFO  : loglevel
  val DEBUG : loglevel
  val TRACE : loglevel
  val ALL   : loglevel
  val log_level_config : loglevel Config.T
  val log : Proof.context -> loglevel -> ('a -> {}) -> 'a -> {}
  val log_fatal : Proof.context -> ('a -> {}) -> 'a -> {}
  val log_err : Proof.context -> ('a -> {}) -> 'a -> {}
  val log_warn : Proof.context -> ('a -> {}) -> 'a -> {}
  val log_info : Proof.context -> ('a -> {}) -> 'a -> {}
  val log_debug : Proof.context -> ('a -> {}) -> 'a -> {}
  val log_trace : Proof.context -> ('a -> {}) -> 'a -> {}
end

structure Log : LOG =
struct

type loglevel = int
(* int values for different log levels*)
val OFF   = 0
val FATAL = 100
val ERR   = 200
val WARN  = 300
val INFO  = 400
val DEBUG = 500
val TRACE = 600
val ALL   = 1000

(* setup for config value log_level, keeps current log level in context *)
val log_level_config = Attrib.setup_config_int @{binding \<open>log_level\<close>} (K ERR)

(* general logging function, prints message using print_f if current log_level \<ge> lvl *)
fun log ctxt custom_lvl print_f = if custom_lvl < Config.get ctxt log_level_config then print_f else K ()

(* logging functions for different log levels *)
fun log_fatal ctxt = log ctxt FATAL
fun log_err ctxt = log ctxt ERR
fun log_warn ctxt = log ctxt WARN
fun log_info ctxt = log ctxt INFO
fun log_debug ctxt = log ctxt DEBUG
fun log_trace ctxt = log ctxt TRACE

end
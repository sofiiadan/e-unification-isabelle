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
end

structure Log : LOG =
struct

type loglevel = int
val OFF   = 0
val FATAL = 100
val ERR   = 200
val WARN  = 300
val INFO  = 400
val DEBUG = 500
val TRACE = 600
val ALL   = 1000

val log_level_config = Attrib.setup_config_int @{binding \<open>log_level\<close>} (K ERR)

fun log ctxt lvl print_f msg = if lvl < Config.get ctxt log_level_config then print_f msg else ()


end
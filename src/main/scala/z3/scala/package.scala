package z3

import jnr.ffi.byref.IntByReference
import jnr.ffi.{LibraryLoader, Pointer}

import _root_.scala.collection.mutable
import _root_.scala.language.implicitConversions
import _root_.scala.ref.WeakReference

package object scala {

  @deprecated("Use Z3NumeralIntAST instead.", "4.0a")
  val Z3NumeralAST = Z3NumeralIntAST

  val Z3Wrapper: Z3Interface = LibraryLoader.create(classOf[Z3Interface]).load("z3")
  val runtime = jnr.ffi.Runtime.getRuntime(Z3Wrapper)

  def toggleWarningMessages(enabled: Boolean) : Unit = {
    Z3Wrapper.Z3_toggle_warning_messages(enabled)
  }

  def resetMemory : Unit = {
    Z3Wrapper.Z3_reset_memory()
  }

  private[z3] def ptrToCtx = new mutable.HashMap[Pointer, WeakReference[Z3Context]]()

  private[z3] def registerContext(ptr: Pointer, ctx: Z3Context): Unit = {
    ptrToCtx.put(ptr, WeakReference(ctx))
  }

  private[z3] def unregisterContext(ptr: Pointer): Unit = {
    ptrToCtx.remove(ptr)
  }

  private[z3] def onZ3Error(contextPtr: Pointer, code: Long): Unit = {
    ptrToCtx(contextPtr).get.get.onError(code)
  }

  /** A string representation of the version numbers for Z3, and the API (including bindings) */
  lazy val version : String = {
    val major = new IntByReference()
    val minor = new IntByReference()
    val buildNumber = new IntByReference()
    val revisionNumber = new IntByReference()
    Z3Wrapper.Z3_get_version(major, minor, buildNumber, revisionNumber)
    s"Z3 ${major.getValue}.${minor.getValue} (build ${buildNumber.getValue}, rev. ${revisionNumber.getValue})"
  }

  protected[z3] def toPtrArray(ptrs : Iterable[Z3Pointer]) : Array[Pointer] = {
    ptrs.map(_.ptr).toArray
  }

  protected[z3] def i2ob(value: Int) : Option[Boolean] = value match {
    case -1 => Some(false)
    case 0 => None
    case _ => Some(true)
  }


  def error(any : Any) : Nothing = {
    //Predef.error(any.toString)
    sys.error(any.toString) // 2.9
  }

  implicit def astvectorToSeq(v: Z3ASTVector): Seq[Z3AST] = v.toSeq
}

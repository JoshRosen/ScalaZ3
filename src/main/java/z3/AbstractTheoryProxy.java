package z3;

import jnr.ffi.Pointer;

// Such a class is used to redirect the callbacks from the C library. To the
// proper Scala/Java functions, and to reformat their output so that it looks
// like pointers. At this level, the pointers are still exposed.
public abstract class AbstractTheoryProxy {
    abstract void delete(Pointer tPtr);
    abstract boolean reduceEq(Pointer tPtr, Pointer t1, Pointer t2, Pointer out);
    abstract boolean reduceApp(Pointer tPtr, Pointer fdptr, int argc, Pointer[] args, Pointer out);
    abstract boolean reduceDistinct(Pointer tPtr, int argc, Pointer[] args, Pointer out);
    abstract void newApp(Pointer tPtr, Pointer appPtr);
    abstract void newElem(Pointer tPtr, Pointer elemPtr);
    abstract void initSearch(Pointer tPtr);
    abstract void push(Pointer tPtr);
    abstract void pop(Pointer tPtr);
    abstract void restart(Pointer tPtr);
    abstract void reset(Pointer tPtr);
    abstract boolean finalCheck(Pointer tPtr);
    abstract void newEq(Pointer tPtr, Pointer t1, Pointer t2);
    abstract void newDiseq(Pointer tPtr, Pointer t1, Pointer t2);
    abstract void newAssignment(Pointer tPtr, Pointer pred, boolean polarity);
    abstract void newRelevant(Pointer tPtr, Pointer t);
}

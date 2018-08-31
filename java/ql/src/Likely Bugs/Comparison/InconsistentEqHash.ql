import java

predicate readsField(Callable c, Field f) {
  exists(FieldRead fr | fr.getField() = f and fr.getEnclosingCallable() = c) or
  exists(GetterMethod getter, MethodAccess get |
    getter.accesses(f) and
    get.getMethod() = getter and
    get.getEnclosingCallable() = c
  )
}

from Class c, EqualsMethod e, HashCodeMethod h, Field f
where
  c.fromSource() and
  e.getDeclaringType() = c and
  h.getDeclaringType() = c and
  f.getDeclaringType() = c and
//  f.getAnAccess().getEnclosingCallable() = h and
//  not f.getName().regexpMatch(".*[hH]ash[cC]ode") and
//  not f.getAnAccess().getEnclosingCallable() = e
  readsField(h, f) and
  not readsField(e, f)
select c, "The field $@ is read in $@ but not in $@.", f, f.getName(), h, h.getName(), e, e.getName()

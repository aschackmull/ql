import java

/** An Android Fragment. */
class AndroidFragment extends Class {
  AndroidFragment() { this.getASupertype*().hasQualifiedName("android.app", "Fragment") }
}

/** The method `instantiate` of the class `android.app.Fragment`. */
class FragmentInstantiateMethod extends Method {
  FragmentInstantiateMethod() {
    this.getDeclaringType() instanceof AndroidFragment and
    this.hasName("instantiate")
  }
}

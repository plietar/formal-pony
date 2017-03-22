interface Any

class None
class Foo
class Bar

trait NPair
  fun ref fst(): Any ref
  fun ref snd(): Any ref

interface SPair
  fun ref fst(): Any ref
  fun ref snd(): Any ref

class Pair is NPair
  var x: Foo ref
  var y: Bar ref

  new create() =>
    x = Foo;
    y = Bar

  fun ref fst(): Foo ref => x
  fun ref snd(): Bar ref => y

class Main
  new create() =>
    this.fst(Pair.create());
    this.snd(Pair.create())

  fun ref fst(p: NPair ref) : Any ref =>
    p.fst()

  fun ref snd(p: SPair ref) : Any ref =>
    p.snd()

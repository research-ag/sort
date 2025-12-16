import Prim "mo:⛔";

module {
  public func copy<T>(source : [var T], dest : [var T], from : Nat32, to : Nat32) {
    var i = from;
    while (i < to) {
      let ii = Prim.nat32ToNat(i);
      dest[ii] := source[ii];
      i +%= 1;
    };
  };
}
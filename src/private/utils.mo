import Nat32 "mo:core/Nat32";

module {
  public func copy<T>(source : [var T], dest : [var T], from : Nat32, to : Nat32) {
    var i = from;
    while (i < to) {
      let ii = Nat32.toNat(i);
      dest[ii] := source[ii];
      i +%= 1;
    };
  };
}
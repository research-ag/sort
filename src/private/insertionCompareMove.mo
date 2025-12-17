import Nat32 "mo:core/Nat32";
import Runtime "mo:core/Runtime";
import Order "mo:core/Order";
import Prim "mo:⛔";

module {
  let nat = Prim.nat32ToNat;

  // sort from buffer to dest array at the given offset
  public func insertionSortSmallMove<T>(buffer : [var T], dest : [var T], compare : (T, T) -> Order.Order, newFrom : Nat32, len : Nat32, offset : Nat32) {
    debug assert len > 0;
    switch (len) {
      case (1) {
        dest[nat(offset)] := buffer[nat(newFrom)];
      };
      case (2) {
        let t0 = buffer[nat(newFrom)];
        let t1 = buffer[nat(newFrom +% 1)];
        switch (compare(t1, t0)) {
          case (#less) {
            dest[nat(offset)] := t1;
            dest[nat(offset +% 1)] := t0;
          };
          case (_) {
            dest[nat(offset)] := t0;
            dest[nat(offset +% 1)] := t1;
          };
        };
      };
      case (3) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        let t2 = buffer[nat(newFrom +% 2)];

        switch (compare(t1, t0)) {
          case (#less) {
            let v = t1;
            t1 := t0;
            t0 := v;
          };
          case (_) {};
        };

        switch (compare(t2, t1)) {
          case (#less) {
            switch (compare(t2, t0)) {
              case (#less) {
                dest[nat(offset)] := t2;
                dest[nat(offset +% 1)] := t0;
                dest[nat(offset +% 2)] := t1;
              };
              case (_) {
                dest[nat(offset)] := t0;
                dest[nat(offset +% 1)] := t2;
                dest[nat(offset +% 2)] := t1;
              };
            };
          };
          case (_) {
            dest[nat(offset)] := t0;
            dest[nat(offset +% 1)] := t1;
            dest[nat(offset +% 2)] := t2;
          };
        };
      };
      case (4) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];

        switch (compare(t1, t0)) {
          case (#less) {
            let v = t1;
            t1 := t0;
            t0 := v;
          };
          case (_) {};
        };

        var tv = t2;
        switch (compare(tv, t1)) {
          case (#less) {
            t2 := t1;
            switch (compare(tv, t0)) {
              case (#less) { t1 := t0; t0 := tv };
              case (_) { t1 := tv };
            };
          };
          case (_) {};
        };

        switch (compare(t3, t2)) {
          case (#less) {
            tv := t3;
            t3 := t2;
            switch (compare(tv, t1)) {
              case (#less) {
                t2 := t1;
                switch (compare(tv, t0)) {
                  case (#less) { t1 := t0; t0 := tv };
                  case (_) { t1 := tv };
                };
              };
              case (_) { t2 := tv };
            };
          };
          case (_) {};
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
      };
      case (5) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];

        switch (compare(t1, t0)) {
          case (#less) {
            let v = t1;
            t1 := t0;
            t0 := v;
          };
          case (_) {};
        };
        var tv = t2;
        switch (compare(tv, t1)) {
          case (#less) {
            t2 := t1;
            switch (compare(tv, t0)) {
              case (#less) { t1 := t0; t0 := tv };
              case (_) { t1 := tv };
            };
          };
          case (_) {};
        };
        tv := t3;
        switch (compare(tv, t2)) {
          case (#less) {
            t3 := t2;
            switch (compare(tv, t1)) {
              case (#less) {
                t2 := t1;
                switch (compare(tv, t0)) {
                  case (#less) { t1 := t0; t0 := tv };
                  case (_) { t1 := tv };
                };
              };
              case (_) { t2 := tv };
            };
          };
          case (_) {};
        };
        tv := t4;
        switch (compare(tv, t3)) {
          case (#less) {
            t4 := t3;
            switch (compare(tv, t2)) {
              case (#less) {
                t3 := t2;
                switch (compare(tv, t1)) {
                  case (#less) {
                    t2 := t1;
                    switch (compare(tv, t0)) {
                      case (#less) { t1 := t0; t0 := tv };
                      case (_) { t1 := tv };
                    };
                  };
                  case (_) { t2 := tv };
                };
              };
              case (_) { t3 := tv };
            };
          };
          case (_) {};
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
      };
      case (6) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];
        var t5 = buffer[nat(newFrom +% 5)];

        switch (compare(t1, t0)) {
          case (#less) {
            let v = t1;
            t1 := t0;
            t0 := v;
          };
          case (_) {};
        };
        var tv = t2;
        switch (compare(tv, t1)) {
          case (#less) {
            t2 := t1;
            switch (compare(tv, t0)) {
              case (#less) { t1 := t0; t0 := tv };
              case (_) { t1 := tv };
            };
          };
          case (_) {};
        };
        tv := t3;
        switch (compare(tv, t2)) {
          case (#less) {
            t3 := t2;
            switch (compare(tv, t1)) {
              case (#less) {
                t2 := t1;
                switch (compare(tv, t0)) {
                  case (#less) { t1 := t0; t0 := tv };
                  case (_) { t1 := tv };
                };
              };
              case (_) { t2 := tv };
            };
          };
          case (_) {};
        };
        tv := t4;
        switch (compare(tv, t3)) {
          case (#less) {
            t4 := t3;
            switch (compare(tv, t2)) {
              case (#less) {
                t3 := t2;
                switch (compare(tv, t1)) {
                  case (#less) {
                    t2 := t1;
                    switch (compare(tv, t0)) {
                      case (#less) { t1 := t0; t0 := tv };
                      case (_) { t1 := tv };
                    };
                  };
                  case (_) { t2 := tv };
                };
              };
              case (_) { t3 := tv };
            };
          };
          case (_) {};
        };
        tv := t5;
        switch (compare(tv, t4)) {
          case (#less) {
            t5 := t4;
            switch (compare(tv, t3)) {
              case (#less) {
                t4 := t3;
                switch (compare(tv, t2)) {
                  case (#less) {
                    t3 := t2;
                    switch (compare(tv, t1)) {
                      case (#less) {
                        t2 := t1;
                        switch (compare(tv, t0)) {
                          case (#less) { t1 := t0; t0 := tv };
                          case (_) { t1 := tv };
                        };
                      };
                      case (_) { t2 := tv };
                    };
                  };
                  case (_) { t3 := tv };
                };
              };
              case (_) { t4 := tv };
            };
          };
          case (_) {};
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
        dest[nat(offset +% 5)] := t5;
      };
      case (7) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];
        var t5 = buffer[nat(newFrom +% 5)];
        var t6 = buffer[nat(newFrom +% 6)];

        switch (compare(t1, t0)) {
          case (#less) {
            let v = t1;
            t1 := t0;
            t0 := v;
          };
          case (_) {};
        };
        var tv = t2;
        switch (compare(tv, t1)) {
          case (#less) {
            t2 := t1;
            switch (compare(tv, t0)) {
              case (#less) { t1 := t0; t0 := tv };
              case (_) { t1 := tv };
            };
          };
          case (_) {};
        };
        tv := t3;
        switch (compare(tv, t2)) {
          case (#less) {
            t3 := t2;
            switch (compare(tv, t1)) {
              case (#less) {
                t2 := t1;
                switch (compare(tv, t0)) {
                  case (#less) { t1 := t0; t0 := tv };
                  case (_) { t1 := tv };
                };
              };
              case (_) { t2 := tv };
            };
          };
          case (_) {};
        };
        tv := t4;
        switch (compare(tv, t3)) {
          case (#less) {
            t4 := t3;
            switch (compare(tv, t2)) {
              case (#less) {
                t3 := t2;
                switch (compare(tv, t1)) {
                  case (#less) {
                    t2 := t1;
                    switch (compare(tv, t0)) {
                      case (#less) { t1 := t0; t0 := tv };
                      case (_) { t1 := tv };
                    };
                  };
                  case (_) { t2 := tv };
                };
              };
              case (_) { t3 := tv };
            };
          };
          case (_) {};
        };
        tv := t5;
        switch (compare(tv, t4)) {
          case (#less) {
            t5 := t4;
            switch (compare(tv, t3)) {
              case (#less) {
                t4 := t3;
                switch (compare(tv, t2)) {
                  case (#less) {
                    t3 := t2;
                    switch (compare(tv, t1)) {
                      case (#less) {
                        t2 := t1;
                        switch (compare(tv, t0)) {
                          case (#less) { t1 := t0; t0 := tv };
                          case (_) { t1 := tv };
                        };
                      };
                      case (_) { t2 := tv };
                    };
                  };
                  case (_) { t3 := tv };
                };
              };
              case (_) { t4 := tv };
            };
          };
          case (_) {};
        };
        tv := t6;
        switch (compare(tv, t5)) {
          case (#less) {
            t6 := t5;
            switch (compare(tv, t4)) {
              case (#less) {
                t5 := t4;
                switch (compare(tv, t3)) {
                  case (#less) {
                    t4 := t3;
                    switch (compare(tv, t2)) {
                      case (#less) {
                        t3 := t2;
                        switch (compare(tv, t1)) {
                          case (#less) {
                            t2 := t1;
                            switch (compare(tv, t0)) {
                              case (#less) { t1 := t0; t0 := tv };
                              case (_) { t1 := tv };
                            };
                          };
                          case (_) { t2 := tv };
                        };
                      };
                      case (_) { t3 := tv };
                    };
                  };
                  case (_) { t4 := tv };
                };
              };
              case (_) { t5 := tv };
            };
          };
          case (_) {};
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
        dest[nat(offset +% 5)] := t5;
        dest[nat(offset +% 6)] := t6;
      };
      case (8) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];
        var t5 = buffer[nat(newFrom +% 5)];
        var t6 = buffer[nat(newFrom +% 6)];
        var t7 = buffer[nat(newFrom +% 7)];

        switch (compare(t1, t0)) {
          case (#less) {
            let v = t1;
            t1 := t0;
            t0 := v;
          };
          case (_) {};
        };
        var tv = t2;
        switch (compare(tv, t1)) {
          case (#less) {
            t2 := t1;
            switch (compare(tv, t0)) {
              case (#less) { t1 := t0; t0 := tv };
              case (_) { t1 := tv };
            };
          };
          case (_) {};
        };
        tv := t3;
        switch (compare(tv, t2)) {
          case (#less) {
            t3 := t2;
            switch (compare(tv, t1)) {
              case (#less) {
                t2 := t1;
                switch (compare(tv, t0)) {
                  case (#less) { t1 := t0; t0 := tv };
                  case (_) { t1 := tv };
                };
              };
              case (_) { t2 := tv };
            };
          };
          case (_) {};
        };
        tv := t4;
        switch (compare(tv, t3)) {
          case (#less) {
            t4 := t3;
            switch (compare(tv, t2)) {
              case (#less) {
                t3 := t2;
                switch (compare(tv, t1)) {
                  case (#less) {
                    t2 := t1;
                    switch (compare(tv, t0)) {
                      case (#less) { t1 := t0; t0 := tv };
                      case (_) { t1 := tv };
                    };
                  };
                  case (_) { t2 := tv };
                };
              };
              case (_) { t3 := tv };
            };
          };
          case (_) {};
        };
        tv := t5;
        switch (compare(tv, t4)) {
          case (#less) {
            t5 := t4;
            switch (compare(tv, t3)) {
              case (#less) {
                t4 := t3;
                switch (compare(tv, t2)) {
                  case (#less) {
                    t3 := t2;
                    switch (compare(tv, t1)) {
                      case (#less) {
                        t2 := t1;
                        switch (compare(tv, t0)) {
                          case (#less) { t1 := t0; t0 := tv };
                          case (_) { t1 := tv };
                        };
                      };
                      case (_) { t2 := tv };
                    };
                  };
                  case (_) { t3 := tv };
                };
              };
              case (_) { t4 := tv };
            };
          };
          case (_) {};
        };
        tv := t6;
        switch (compare(tv, t5)) {
          case (#less) {
            t6 := t5;
            switch (compare(tv, t4)) {
              case (#less) {
                t5 := t4;
                switch (compare(tv, t3)) {
                  case (#less) {
                    t4 := t3;
                    switch (compare(tv, t2)) {
                      case (#less) {
                        t3 := t2;
                        switch (compare(tv, t1)) {
                          case (#less) {
                            t2 := t1;
                            switch (compare(tv, t0)) {
                              case (#less) { t1 := t0; t0 := tv };
                              case (_) { t1 := tv };
                            };
                          };
                          case (_) { t2 := tv };
                        };
                      };
                      case (_) { t3 := tv };
                    };
                  };
                  case (_) { t4 := tv };
                };
              };
              case (_) { t5 := tv };
            };
          };
          case (_) {};
        };
        tv := t7;
        switch (compare(tv, t6)) {
          case (#less) {
            t7 := t6;
            switch (compare(tv, t5)) {
              case (#less) {
                t6 := t5;
                switch (compare(tv, t4)) {
                  case (#less) {
                    t5 := t4;
                    switch (compare(tv, t3)) {
                      case (#less) {
                        t4 := t3;
                        switch (compare(tv, t2)) {
                          case (#less) {
                            t3 := t2;
                            switch (compare(tv, t1)) {
                              case (#less) {
                                t2 := t1;
                                switch (compare(tv, t0)) {
                                  case (#less) { t1 := t0; t0 := tv };
                                  case (_) { t1 := tv };
                                };
                              };
                              case (_) { t2 := tv };
                            };
                          };
                          case (_) { t3 := tv };
                        };
                      };
                      case (_) { t4 := tv };
                    };
                  };
                  case (_) { t5 := tv };
                };
              };
              case (_) { t6 := tv };
            };
          };
          case (_) {};
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
        dest[nat(offset +% 5)] := t5;
        dest[nat(offset +% 6)] := t6;
        dest[nat(offset +% 7)] := t7;
      };
      case (_) Runtime.trap("insertionSortSmall for len > 8 is not implemented.");
    };
  };
};

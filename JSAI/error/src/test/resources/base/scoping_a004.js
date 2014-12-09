var x=1;
var y=0;
if (true) {
    print(">x1"); print(x); print(">y1"); print(y);
    var x=2;
    print(">x2"); print(x);
    if (true) {
        var x=3;
        print(">>x1"); print(x);
        y = y + x;
        print(">>y2"); print(y);
    }
    print(">x3"); print(x); print(">y3"); print(y);
    y = y + x;
    print(">y4"); print(y);
}
print("x1"); print(x); print("y1"); print(y);
y = y + x;
print("y2"); print(y);
y //should be 9!

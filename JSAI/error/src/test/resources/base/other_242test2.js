
//Example from CS242 at Stanford.
//toString is implicitly called; should return "a10"
//As of 9/23/2012 this is buggy in the s.s. abstract interpreter.

var y = "a";
var x = { toString : function() { print("xtoString"); print(y); return y; }};
var s = x.toString(); print(s);
x = x + 10;
print(x);


var a = Array(0);
print(a[0]);
print(a.length);

var b = Array(1, 2, 3);
print(b[2]);
print(b.length);

var c = new Array(0);
print(c[0]);
print(c.length);

var d = new Array(1,2,3);
print(d[2]);
print(d.length);

var e = Array();
print(e[0]);
print(e.length);

var f = new Array(); 
print(f[0]);
print(f.length);

var x = Array; 

var g = x(0);
print(g[0]);
print(g.length);

var h = x(1, 2, 3);
print(h[2]);
print(h.length);

var i = new x(0); 
print(i[0]);
print(i.length);

var j = new x(1,2,3);
print(j[1]);
print(j.length);

var k = x();
print(k[0]);
print(k.length);

var l = new x();
print(l[0]);
print(l.length);

// function foo() {}

// if (...) x = Array; else x = foo; 

// x(0)

// x(1, 2, 3)

// new x(0)

// new x(1,2,3)

// x()

// new x()


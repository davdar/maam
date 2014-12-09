function bar(x) {
    this.x = x;
}

function foo() {
    return bar;
}

print(new foo(5).x);

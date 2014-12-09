function foo() {
    try {
        throw 5;
    } finally {
        print("FINALLY");
    }
}

try {
    foo();
} catch (x) {
    print(x);
}

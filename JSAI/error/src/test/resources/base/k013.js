var counter = 0;
var obj = {foo: 10, bar: 10};
var field = {toString: function () {
        counter += 1;
        return (counter == 1) ? "foo" : "bar";
    }
};
print(counter);
obj[field] += 1;
print(counter);
print("foo: " + obj.foo);
print("bar: " + obj.bar);

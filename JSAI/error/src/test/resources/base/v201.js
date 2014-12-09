// this is the Y combinator
// taken from "http://int3.github.io/metajs/""

var Y = function (F) {
  return (function (x) {
    return F(function (y) { return x(x)(y); });
  })(function (x) {
    return F(function (y) { return x(x)(y); });
  });
};

var factorial = function (myself) {
  return function(n) {
    return n === 0 ? 1 : n * myself(n-1);
  };
};

var result = Y(factorial)(4);
print(result);

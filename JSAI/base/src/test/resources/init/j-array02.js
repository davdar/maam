x = [1,2,3,4,5]


s = x.toString()
print(s)

s = x.concat().toString()
print(s)

s = x.concat(undefined).toString()
print(s)

s = [].concat(x, ["a","b","c"], 5, [null], [["six"]]).toString()
print(s)


s = x.join()
print(s)

s = x.join(undefined)
print(s)

s = x.join(" ")
print(s)


x = [1,2,3,4,5]
n = x.push()
print(n)
s = x.toString()
print(s)

x = [1,2,3,4,5]
n = x.push(undefined)
print(n)
s = x.toString()
print(s)

x = [1,2,3,4,5]
n = x.push(1,2,3,["array"])
print(n)
s = x.toString()
print(s)


x = [1,2,3,4,5]
n = x.pop()
print(n)
s = x.toString()
print(s)


x = [1,2,3,4,5]
y = x.reverse()
s = x.toString()
print(s)
s = y.toString()
print(s)


x = [1,2,3,4,5]
n = x.shift()
print(n)
s = x.toString()
print(s)

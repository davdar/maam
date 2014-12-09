/* Continue test */
var flag = true;
var str = "";

l1:while (flag) {
    print("l1:entered")
    l2:while (flag) {
        print("l2:entered")
        l3:while(flag) {
            print("l3:entered")
            l4:while (flag) {
                print("l4:entered")
                str = "PASS";
                break; // Must leave l4
                print("l4:slipped past break")
                str = "FAILED";
            }
            print("l4:exit")
            break l2;
            print("l3:slipped past break")
            str = "FAILED";
        }
        print("should have broken out of l2 not l3!")
        str = "FAILED";
    }
    print("l2:exit")
    break l1;
    print("l1:slipped past break")
    str = "FAILED";
}
print("l1: exit")

print(str)
str; // Must be PASS

var array = [4, 5, 2, 6, 7];
var str = array.join(",");
print(str);

function insertionSort(sortMe) {
   print("insert");
   for (var i = 0, j, tmp; i < sortMe.length; ++i) {
      print("outer");
      print(i);
      tmp = sortMe[i];
      print(tmp);
      for (j = i - 1; j >= 0 && sortMe[j] > tmp; --j) {
         print("inner");
         print(j);
         var tmp2 = sortMe[j];
         print(tmp2);
         sortMe[j + 1] = tmp2;
      }
      sortMe[j + 1] = tmp;
   }
}

insertionSort(array);
str = array.join(",");
print(str);
print(array[0]); print(array[1]); print(array[2]); print(array[3]); print(array[4]);


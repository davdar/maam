function partition(arr, begin, end, pivot)
{
    print("partition");
    print(begin); print(end); print(pivot);
    var piv=arr[pivot];
    swap(arr, pivot, end-1);
    var store=begin;
    var ix;
    for(ix=begin; ix<end-1; ++ix) {
        print("loop");
        print(ix);
        if(arr[ix]<=piv) {
            print("arr[ix] <= piv");
            swap(arr,store, ix);
            print(store);
            ++store;
            print(store);
        }
    }
    swap(arr,end-1, store);

    print("returning");
    print(store);
    return store;
}

function swap(arr, a, b)
{
    print("swapping");
    print(a); print(b);
    var arr_str = arr.join(",")
    print(arr_str);
    var tmp=arr[a];
    arr[a]=arr[b];
    arr[b]=tmp;
    var arr_str = arr.join(",")
    print(arr_str);
    print("done swapping");
}

function qsort(arr, begin, end)
{
    print("qsort");
    if(end-1>begin) {
        var pivot=begin;

        pivot=partition(arr, begin, end, pivot);

        qsort(arr, begin, pivot);
        qsort(arr, pivot+1, end);
    }
    print("qsort returning");
    var arr_str = arr.join(",");
    print(arr_str);
    return arr;
}

function quick_sort(arr)
{
    print(arr.length);
    return qsort(arr, 0, arr.length);
}

stuff = [1,77,-2,13,-12,3,9,11,0,4,5,-3,8,3,3,7];
var out = quick_sort(stuff);
var res = out[0]; //-12
print(res);



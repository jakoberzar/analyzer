//PARAM: --sets ana.activated[+] available
#include "stdio.h"

int f(int n) {
    if (n <= 1) {
        printf("End!");
        return 1;
    }
    return n * f(n - 1);
}

int main(){
    int x = 3;
    int y = 4;
    int d = x + y;
    int z = 2 * d + y;
    scanf("%d", &d);
    z = 2 * d + y;
    d = f(d);
    z = 2 * d + y;
    f(&d);

    if(d){
        z = 2 * d + y;
        x = d + y;
    } else {
        x = d + y;
    }

    return 0;
}

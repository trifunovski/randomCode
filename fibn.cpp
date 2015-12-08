#include <iostream>

using namespace std;

int fibn(int f1, int f2, int n){
        if(n==0)
                return f1;
        if(n==1)
                return f2;
        return fibn(f2,f1+f2,n-1);
}

int main(){
        int n;
        cin>>n;
        cout<<fibn(0,1,n)<<endl;
        return 0;
}

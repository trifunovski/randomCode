#include <iostream>

using namespace std;

template <class T>class ArrayList {
T array[4];
private:
void reUp(){
        int size = sizeof(array)/sizeof(array[0]);
        T newArray[size*2];
        for(int i=0; i<size; i++)
                newArray[i]=array[i];
        array=newArray;
}
public:
ArrayList(){

}
void add(T elem){
        int size = sizeof(array)/sizeof(array[0]);
        if(size==100)
                reUp();
        else
                array[size]=elem;
}
};

int main(){
        ArrayList<int> l1;
        l1.add(5);
        l1.add(20);
        return 0;
}

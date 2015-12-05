#include <iostream>

using namespace std;


struct rect{
  int xbot,ybot,width,height,xtop,ytop;
  rect(x1,y1,w1,h1){
    x=x1;
    y=y1;
    width=w1;
    height=h1;
    xtop=x+width;
    ytop=y+height;
  }
}

int main(){
  int x1,y1,w1,h1,x2,y2,w2,h2;

  cin>>x1>>y1>>w1>>h1>>x2>>y2>>w2>>h2;

  rect rect1 = rect(x1,y1,w1,h1);
  rect rect2 = rect(x2,y2,w2,h2);

  if((rect1.x<rect2.x && rect1.xtop>rect2.x) || (rect1.x<rect2.xtop && rect1.xtop>rect2.xtop)){

  }
  else{
    cout<<"no intersection"<<endl;
  }



}

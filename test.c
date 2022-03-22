//This program is zodiac.c
#include<stdio.h>

unsigned int b1=1, b2=1, b3=1, b4=1;
int d1, d2, d3, d4;
int e1[2], e2[2];
extern int ex1, ex2;
const extern int ex3;

typedef struct { int x, y; } Point;
Point f1, f2;

int extFunc(int a1, int a2);

int func(int a1) {
    return a1;
}

int func1(int date, int ch, int a1, int a2, int a3, int a4) {
    int c1, c2, c3, c4;
    if ((a1>1) && (a2>1)) printf("test predicate 0.");
    else if (a1==a2==b3==b4) printf("test predicate 0.");
    if ((a1==a2)==(b3==b4)) printf("test predicate 0.");
    if (((a1>=22) || (b2==2)) != ((b3>=22) || (b4==2)))
        printf("test predicate 1.1");
    if (((a1>=22) && (b2==2)) != (d3==2) != (d4==3))
        printf("test predicate 4");
    if (ex1>0 && ex2>0 && ex3>0)
        printf("test predicate 5");
    return a1;
}

int func2(int a1, int a2, int a3, int a4) {
if (((a1>=22) || (a2==2)) != ((a3>=22) || (a4==1)))
printf("Predicate 0\n");
else
printf("Predicate 0.1\n");
if (((a1>=22) || (a2==2)) != ((a3>=22) || (a4==2)))
printf("Predicate 1\n");
else
printf("Predicate 1.1\n");

switch (a1) {
case 0 : break;
case 1 : break;
case 2 : break;
default : break;
}

if ((a1>=22) && ((a2==2) || (a3<=21)))
printf("Predicate 2");
if (((a1>=22) && (a2==2)) != (a3==2) != (a4==3))
printf("Predicate 3");
return a1;
}

int func3(int a1, int a2, int a3, int a4, int a5[5]) {
//if (a1>0) return a1;
//if (a2>0) return a2;

if (((a1>=22) || (a2==2)) != ((a3>=22) || (a4==1)))
printf("Predicate 0\n");
if (((a1>=22) || (a2==2)) != ((a3>=22) || (a4==2)))
printf("Predicate 1\n");
if ((a1>=22) && ((a2==2) || (a3<=21)))
printf("Predicate 2");
if (((a1>=22) && (a2==2)) != (a3==2) != (a4==3))
printf("Predicate 3");
    return a1;
}

int func4(int a1, int a2, int a3, int a4) {
if (((a1++>=22) || (a2==2)) != ((a3>=22) || (a4==1)))
printf("Predicate 0\n");
else
printf("Predicate 0.1\n");
if (((a1>=22) || (a2==2)) != ((a3>=22) || (a4==2)))
printf("Predicate 1\n");
else
printf("Predicate 1.1\n");

switch (a1) {
case 0 : break;
case 1 : break;
case 2 : break;
default : break;
}

if ((a1>=22) && ((a2==2) || (a3<=21)))
printf("Predicate 2");
if (((a1>=22) && (a2==2)) != (a3==2) != (a4==3))
printf("Predicate 3");
return a1;
}

int func5(int date, int ch, int a1, int a2, int a3, int a4) {
    int c1, c2, c3, c4;
    if ((a1>1) && (a2>1)) printf("test predicate 0.");
    if (a1==a2==b3==b4) printf("test predicate 0.");
    if ((a1==a2)==(b3==b4)) printf("test predicate 0.");
    if (((a1>=22) || (b2==2)) != ((b3>=22) || (b4==2)))
        printf("test predicate 1.1");
    if (((a1>=22) && (b2==2)) != (d3==2) != (d4==3))
        printf("test predicate 4");
    return a1;
}

int main() {
int  date,ch;
int  a1;
int  a2;
int  a3;
int  a4;

printf("ENTER DATE OF BIRTH AND THEN MONTH NO. codewithc");
//scanf("%d %d",&date,&ch);

if (a1==a2==a3==a4) printf("test predicate 0.");
if ((a1==a2)==(a3==a4)) printf("test predicate 0.");
if (func(a1)==func(a2)) printf("test predicate 0.");
if (!(!(!(date>=22))||!(a1<0))) printf("test predicate 0.");
if (!(!(!(date>=22))||!(a1<0))==!(!(date>=22)||!(a1<0))) printf("test predicate 0.");
if ((date>=22) && (ch==2)) {
    if ((a1>=10) || (a2<=5))
      printf("test predicate 0.1");
    else
      printf("test predicate 0.2");
    printf("test predicate 0");
}

if ((date>=22) != ((ch==2) != (a1==2)))
printf("test predicate 1");
if (((date>=22) || (ch==2)) != ((a1>=22) || (a2==2)))
printf("test predicate 1.1");
if ((date>=22) && ((ch==2) || (a1<=21)))
printf("test predicate 2");
if (((date>=22) && (ch==2)) != (a1==2) != (a2==3))
printf("test predicate 4");


int i=0;
for (i=0; i<a2; i++) printf("%d", a2);

i=0;
while (i<a3) {
    i++;
    printf("%d", a3);
}

i=0;
do {
    i++;
    printf("%d", a4);
} while (i<a4);

switch (a1) {
    case 0:
    case 1: break;
    case 2:
    default: printf("%d", a1);
}

switch (a1) {
    default: printf("%d", a1);
}

switch (a1) {
    case 0: break;
}

switch (a1) {
    case 0:
    case 1: break;
}

return 0;
}

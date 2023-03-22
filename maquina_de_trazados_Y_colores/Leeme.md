# Librería gráfica Máquina de Trazados

 Esta es la distribución del la librería maquinas de trazados. Esta
 distribución contiene tres directorios:
 
 * **doc**: Documentación de la Máquina de trazados, generada con javadoc.
 * **lib**: Contiene el marchivo mt.jar que corresponde a la maquina de trazados. 
 * **ejemplos**: Ejemplos de como se usa la maquina de trazados. 

La documentación de la librería la puede observar en el archivo *doc/index.html*

Esta librería contiene una clase enumeración llamada *Colores*, que contine los colores disponibles en la máquina de trazdos. A continuación se muestra el código de la clase *Colores*:

```
public enum Colores {
    BLACK,
    BLUE,
    CYAN,
    DARK_GRAY,
    GRAY,
    GREEN,
    LIGHT_GRAY,
    MAGENTA,
    ORANGE,
    PINK,
    RED,
    WHITE,
    YELLOW
}
``` 

Para compilar los ejemplos vaya a la carpeta *ejemplos* y ejecute el comando:

```
openjml --compile -cp ../lib/maquinaTrazados-v0.1.jar  *.java
``` 

Para correr los ejemplos ejecute los siguientes comandos:


```
>openjml-java -cp ../lib/maquinaTrazados-v0.1.jar:. PruebaFuente
``` 

```
>openjml-java -cp ../lib/maquinaTrazados-v0.1.jar:. PruebaPoligonos.java 
``` 

```
>openjml-java -cp ../lib/maquinaTrazados-v0.1.jar:. PruebaOvalosRectangulosLineas
``` 

En este ejemplo se ejecuta una animación de varios segundos. Espero a que la ventana cierre y termine la ejecución. Se ejecuta:

```
>openjml-java -cp ../lib/maquinaTrazados-v0.1.jar:. PruebaRectangulosDeColores
``` 


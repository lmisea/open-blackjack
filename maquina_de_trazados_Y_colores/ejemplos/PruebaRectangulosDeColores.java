import java.util.concurrent.TimeUnit;

public class PruebaRectangulosDeColores {

    public static void pausarEjecucion(int segundos) {
	try {
	    TimeUnit.SECONDS.sleep(segundos);
	} catch(Exception e) {
	    System.out.println("Error pausando el programa.");
	};
    }

    public static void main(String[] args) {
	MaquinaDeTrazados mt = new MaquinaDeTrazados(500, 300, "Prueba de Rectangulos", Colores.DARK_GRAY);
	System.out.println("XMAX: "+mt.XMAX);
	System.out.println("YMAX: "+mt.YMAX);
	mt.dibujarString("Rojo", 130, 40, Colores.RED);
	mt.dibujarString("Verde", 130, 65,  Colores.GREEN);
	mt.dibujarString("Blue", 130, 90,  Colores.BLUE);
	mt.dibujarString("Magenta", 130, 115,  Colores.MAGENTA);
	mt.mostrar();
	pausarEjecucion(3);
	mt.dibujarRectanguloLleno(15, 25, 100, 20, Colores.RED);
	mt.dibujarRectanguloLleno(15, 50, 100, 20, Colores.GREEN);
	mt.dibujarRectanguloLleno(15, 75, 100, 20, Colores.BLUE);
	mt.dibujarRectanguloLleno(15, 100, 100, 20, Colores.MAGENTA);
	mt.repintar();
	pausarEjecucion(3);
	mt.limpiar();
	pausarEjecucion(3);
	mt.terminar();
    }
}
